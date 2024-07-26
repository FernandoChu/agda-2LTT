# Automorphisms

```agda
module foundation.automorphismsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.setsᵉ

open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Anᵉ automorphismᵉ onᵉ aᵉ typeᵉ `A`ᵉ isᵉ anᵉ equivalenceᵉ `Aᵉ ≃ᵉ A`.ᵉ Weᵉ willᵉ justᵉ reuseᵉ theᵉ
infrastructureᵉ ofᵉ equivalencesᵉ forᵉ automorphisms.ᵉ

## Definitions

### The type of automorphisms on a type

```agda
Autᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
Autᵉ Yᵉ = Yᵉ ≃ᵉ Yᵉ

is-set-Autᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-setᵉ Aᵉ → is-setᵉ (Autᵉ Aᵉ)
is-set-Autᵉ Hᵉ = is-set-equiv-is-setᵉ Hᵉ Hᵉ

Aut-Setᵉ : {lᵉ : Level} → Setᵉ lᵉ → Setᵉ lᵉ
pr1ᵉ (Aut-Setᵉ Aᵉ) = Autᵉ (type-Setᵉ Aᵉ)
pr2ᵉ (Aut-Setᵉ Aᵉ) = is-set-Autᵉ (is-set-type-Setᵉ Aᵉ)

Aut-Pointed-Typeᵉ : {lᵉ : Level} → UUᵉ lᵉ → Pointed-Typeᵉ lᵉ
pr1ᵉ (Aut-Pointed-Typeᵉ Aᵉ) = Autᵉ Aᵉ
pr2ᵉ (Aut-Pointed-Typeᵉ Aᵉ) = id-equivᵉ
```