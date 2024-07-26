# The Zariski locale

```agda
module commutative-algebra.zariski-localeᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.intersections-radical-ideals-commutative-ringsᵉ
open import commutative-algebra.joins-radical-ideals-commutative-ringsᵉ
open import commutative-algebra.poset-of-radical-ideals-commutative-ringsᵉ

open import foundation.universe-levelsᵉ

open import order-theory.large-framesᵉ
open import order-theory.large-localesᵉ
```

</details>

## Idea

Theᵉ **Zariskiᵉ locale**ᵉ ofᵉ aᵉ
[commutativeᵉ ring](commutative-algebra.commutative-rings.mdᵉ) `A`ᵉ isᵉ theᵉ
[largeᵉ locale](order-theory.large-locales.mdᵉ) consistingᵉ ofᵉ
[radicalᵉ ideals](commutative-algebra.radical-ideals-commutative-rings.mdᵉ) ofᵉ
`A`.ᵉ Ourᵉ proofᵉ ofᵉ theᵉ factᵉ thatᵉ meetsᵉ distributeᵉ overᵉ arbitraryᵉ joinsᵉ usesᵉ theᵉ
factᵉ thatᵉ theᵉ intersectionᵉ `Iᵉ ∩ᵉ J`ᵉ ofᵉ radicalᵉ idealsᵉ isᵉ equivalentlyᵉ describedᵉ
asᵉ theᵉ radicalᵉ idealᵉ `√ᵉ IJ`ᵉ ofᵉ theᵉ
[productᵉ ideal](commutative-algebra.products-ideals-commutative-rings.md).ᵉ

## Definition

### The Zariski frame

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  where

  zariski-frame-Commutative-Ringᵉ :
    Large-Frameᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) l1ᵉ
  large-poset-Large-Frameᵉ
    zariski-frame-Commutative-Ringᵉ =
    radical-ideal-Commutative-Ring-Large-Posetᵉ Aᵉ
  is-large-meet-semilattice-Large-Frameᵉ
    zariski-frame-Commutative-Ringᵉ =
    is-large-meet-semilattice-radical-ideal-Commutative-Ringᵉ Aᵉ
  is-large-suplattice-Large-Frameᵉ zariski-frame-Commutative-Ringᵉ =
    is-large-suplattice-radical-ideal-Commutative-Ringᵉ Aᵉ
  distributive-meet-sup-Large-Frameᵉ zariski-frame-Commutative-Ringᵉ =
    distributive-intersection-join-family-of-radical-ideals-Commutative-Ringᵉ Aᵉ
```

### The Zariski locale

```agda
module _
  {l1ᵉ : Level} (Aᵉ : Commutative-Ringᵉ l1ᵉ)
  where

  zariski-locale-Commutative-Ringᵉ :
    Large-Localeᵉ (λ l2ᵉ → l1ᵉ ⊔ lsuc l2ᵉ) (λ l2ᵉ l3ᵉ → l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) l1ᵉ
  zariski-locale-Commutative-Ringᵉ = zariski-frame-Commutative-Ringᵉ Aᵉ
```