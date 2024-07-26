# Double counting

```agda
module univalent-combinatorics.double-countingᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Givenᵉ twoᵉ countingsᵉ ofᵉ theᵉ sameᵉ type,ᵉ weᵉ obtainᵉ theᵉ sameᵉ numberᵉ ofᵉ itsᵉ elements.ᵉ
Likewise,ᵉ givenᵉ twoᵉ countingsᵉ ofᵉ equivalentᵉ types,ᵉ weᵉ obtainᵉ theᵉ sameᵉ numberᵉ ofᵉ
theirᵉ elements.ᵉ

```agda
abstract
  double-counting-equivᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (count-Aᵉ : countᵉ Aᵉ)
    (count-Bᵉ : countᵉ Bᵉ) (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
    Idᵉ (number-of-elements-countᵉ count-Aᵉ) (number-of-elements-countᵉ count-Bᵉ)
  double-counting-equivᵉ (kᵉ ,ᵉ fᵉ) (lᵉ ,ᵉ gᵉ) eᵉ =
    is-equivalence-injective-Finᵉ (inv-equivᵉ gᵉ ∘eᵉ eᵉ ∘eᵉ fᵉ)

abstract
  double-countingᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (count-Aᵉ count-A'ᵉ : countᵉ Aᵉ) →
    Idᵉ (number-of-elements-countᵉ count-Aᵉ) (number-of-elements-countᵉ count-A'ᵉ)
  double-countingᵉ count-Aᵉ count-A'ᵉ =
    double-counting-equivᵉ count-Aᵉ count-A'ᵉ id-equivᵉ
```