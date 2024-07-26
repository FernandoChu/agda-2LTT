# Separated types

```agda
module foundation.separated-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.subuniversesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Considerᵉ aᵉ [subuniverse](foundation.subuniverses.mdᵉ) `P`.ᵉ Aᵉ typeᵉ `A`ᵉ isᵉ saidᵉ to
beᵉ **`P`-separated**ᵉ ifᵉ itsᵉ [identityᵉ types](foundation-core.identity-types.mdᵉ)
areᵉ in `P`.ᵉ Similarly,ᵉ aᵉ typeᵉ `A`ᵉ isᵉ saidᵉ to beᵉ **essentiallyᵉ `P`-separated**ᵉ ifᵉ
itsᵉ [identityᵉ types](foundation-core.identity-types.mdᵉ) areᵉ
[equivalent](foundation-core.equivalences.mdᵉ) to typesᵉ in `P`.ᵉ

## Definitions

### The predicate of being separated

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  where

  is-separated-Propᵉ : (Xᵉ : UUᵉ l1ᵉ) → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  is-separated-Propᵉ Xᵉ = Π-Propᵉ Xᵉ (λ xᵉ → Π-Propᵉ Xᵉ (λ yᵉ → Pᵉ (xᵉ ＝ᵉ yᵉ)))

  is-separatedᵉ : (Xᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-separatedᵉ Xᵉ = type-Propᵉ (is-separated-Propᵉ Xᵉ)

  is-prop-is-separatedᵉ : (Xᵉ : UUᵉ l1ᵉ) → is-propᵉ (is-separatedᵉ Xᵉ)
  is-prop-is-separatedᵉ Xᵉ = is-prop-type-Propᵉ (is-separated-Propᵉ Xᵉ)
```

### The predicate of being essentially separated

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  where

  is-essentially-separatedᵉ : {l3ᵉ : Level} (Xᵉ : UUᵉ l3ᵉ) → UUᵉ (lsuc l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-essentially-separatedᵉ Xᵉ =
    (xᵉ yᵉ : Xᵉ) → is-essentially-in-subuniverseᵉ Pᵉ (xᵉ ＝ᵉ yᵉ)
```