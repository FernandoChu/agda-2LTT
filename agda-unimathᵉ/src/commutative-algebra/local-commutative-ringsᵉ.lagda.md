# Local commutative rings

```agda
module commutative-algebra.local-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import ring-theory.local-ringsᵉ
open import ring-theory.ringsᵉ
```

</details>

## Idea

Aᵉ **localᵉ ring**ᵉ isᵉ aᵉ ringᵉ suchᵉ thatᵉ wheneverᵉ aᵉ sumᵉ ofᵉ elementsᵉ isᵉ invertible,ᵉ
thenᵉ oneᵉ ofᵉ itsᵉ summandsᵉ isᵉ invertible.ᵉ Thisᵉ impliesᵉ thatᵉ theᵉ noninvertibleᵉ
elementsᵉ formᵉ anᵉ ideal.ᵉ However,ᵉ theᵉ lawᵉ ofᵉ excludedᵉ middleᵉ isᵉ neededᵉ to showᵉ
thatᵉ anyᵉ ringᵉ ofᵉ whichᵉ theᵉ noninvertibleᵉ elementsᵉ formᵉ anᵉ idealᵉ isᵉ aᵉ localᵉ ring.ᵉ

## Definition

```agda
is-local-prop-Commutative-Ringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) → Propᵉ lᵉ
is-local-prop-Commutative-Ringᵉ Aᵉ = is-local-prop-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

is-local-Commutative-Ringᵉ : {lᵉ : Level} → Commutative-Ringᵉ lᵉ → UUᵉ lᵉ
is-local-Commutative-Ringᵉ Aᵉ = is-local-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

is-prop-is-local-Commutative-Ringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) → is-propᵉ (is-local-Commutative-Ringᵉ Aᵉ)
is-prop-is-local-Commutative-Ringᵉ Aᵉ =
  is-prop-is-local-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ)

Local-Commutative-Ringᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
Local-Commutative-Ringᵉ lᵉ = Σᵉ (Commutative-Ringᵉ lᵉ) is-local-Commutative-Ringᵉ

module _
  {lᵉ : Level} (Aᵉ : Local-Commutative-Ringᵉ lᵉ)
  where

  commutative-ring-Local-Commutative-Ringᵉ : Commutative-Ringᵉ lᵉ
  commutative-ring-Local-Commutative-Ringᵉ = pr1ᵉ Aᵉ

  ring-Local-Commutative-Ringᵉ : Ringᵉ lᵉ
  ring-Local-Commutative-Ringᵉ =
    ring-Commutative-Ringᵉ commutative-ring-Local-Commutative-Ringᵉ

  set-Local-Commutative-Ringᵉ : Setᵉ lᵉ
  set-Local-Commutative-Ringᵉ = set-Ringᵉ ring-Local-Commutative-Ringᵉ

  type-Local-Commutative-Ringᵉ : UUᵉ lᵉ
  type-Local-Commutative-Ringᵉ =
    type-Ringᵉ ring-Local-Commutative-Ringᵉ

  is-local-commutative-ring-Local-Commutative-Ringᵉ :
    is-local-Commutative-Ringᵉ commutative-ring-Local-Commutative-Ringᵉ
  is-local-commutative-ring-Local-Commutative-Ringᵉ = pr2ᵉ Aᵉ
```