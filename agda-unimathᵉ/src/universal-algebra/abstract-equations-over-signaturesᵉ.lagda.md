# Abstract equations over signatures

```agda
module universal-algebra.abstract-equations-over-signaturesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import universal-algebra.signaturesᵉ
open import universal-algebra.terms-over-signaturesᵉ
```

</details>

## Idea

Anᵉ **abstractᵉ equation**ᵉ overᵉ aᵉ signatureᵉ `Sg`ᵉ isᵉ aᵉ statementᵉ ofᵉ aᵉ formᵉ "`x`ᵉ
equalsᵉ `y`",ᵉ where `x`ᵉ andᵉ `y`ᵉ areᵉ termsᵉ overᵉ `Sg`.ᵉ Thus,ᵉ theᵉ data ofᵉ anᵉ
abstract equationᵉ isᵉ simplyᵉ twoᵉ termsᵉ overᵉ aᵉ commonᵉ signature.ᵉ

## Definitions

### Abstract equations

```agda
module _
  {l1ᵉ : Level} (Sgᵉ : signatureᵉ l1ᵉ)
  where

  Abstract-Equationᵉ : UUᵉ l1ᵉ
  Abstract-Equationᵉ = Termᵉ Sgᵉ ×ᵉ Termᵉ Sgᵉ

  lhs-Abstract-Equationᵉ : Abstract-Equationᵉ → Termᵉ Sgᵉ
  lhs-Abstract-Equationᵉ = pr1ᵉ

  rhs-Abstract-Equationᵉ : Abstract-Equationᵉ → Termᵉ Sgᵉ
  rhs-Abstract-Equationᵉ = pr2ᵉ
```