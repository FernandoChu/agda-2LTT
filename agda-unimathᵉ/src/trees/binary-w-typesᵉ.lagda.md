# Binary W-types

```agda
module trees.binary-w-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Considerᵉ aᵉ typeᵉ `A`ᵉ andᵉ twoᵉ typeᵉ familiesᵉ `B`ᵉ andᵉ `C`ᵉ overᵉ `A`.ᵉ Thenᵉ weᵉ obtainᵉ
theᵉ polynomialᵉ functorᵉ

```text
  Xᵉ Yᵉ ↦ᵉ Σᵉ (aᵉ : A),ᵉ (Bᵉ aᵉ → Xᵉ) ×ᵉ (Cᵉ aᵉ → Yᵉ)
```

in twoᵉ variablesᵉ `X`ᵉ andᵉ `Y`.ᵉ Byᵉ diagonalising,ᵉ weᵉ obtainᵉ theᵉ
[polynomialᵉ endofunctor](trees.polynomial-endofunctors.mdᵉ)

```text
  Xᵉ ↦ᵉ Σᵉ (aᵉ : A),ᵉ (Bᵉ aᵉ → Xᵉ) ×ᵉ (Cᵉ aᵉ → X).ᵉ
```

whichᵉ mayᵉ beᵉ broughtᵉ to theᵉ exactᵉ formᵉ ofᵉ aᵉ polynomialᵉ endofunctorᵉ ifᵉ oneᵉ wishesᵉ
to do soᵉ:

```text
  Xᵉ ↦ᵉ Σᵉ (aᵉ : A),ᵉ (Bᵉ aᵉ +ᵉ Cᵉ aᵉ → X).ᵉ
```

Theᵉ {{#conceptᵉ "binaryᵉ W-type"ᵉ Agda=binary-𝕎ᵉ}} isᵉ theᵉ W-typeᵉ `binary-𝕎`ᵉ
associatedᵉ to thisᵉ polynomialᵉ endofunctor.ᵉ Inᵉ otherᵉ words,ᵉ itᵉ isᵉ theᵉ inductive
typeᵉ generatedᵉ byᵉ

```text
  make-binary-𝕎ᵉ : (aᵉ : Aᵉ) → (Bᵉ aᵉ → binary-𝕎ᵉ) → (Cᵉ aᵉ → binary-𝕎ᵉ) → binary-𝕎.ᵉ
```

Theᵉ binaryᵉ W-typeᵉ isᵉ equivalentᵉ to theᵉ
[hereditaryᵉ W-types](trees.hereditary-w-types.mdᵉ) viaᵉ anᵉ
[equivalence](foundation.equivalences.mdᵉ) thatᵉ generalizesᵉ theᵉ equivalenceᵉ ofᵉ
planeᵉ treesᵉ andᵉ fullᵉ binaryᵉ planeᵉ trees,ᵉ whichᵉ isᵉ aᵉ wellᵉ knownᵉ equivalenceᵉ usedᵉ
in theᵉ studyᵉ ofᵉ theᵉ
[Catalanᵉ numbers](elementary-number-theory.catalan-numbers.md).ᵉ

## Definitions

### Binary W-types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ) (Cᵉ : Aᵉ → UUᵉ l3ᵉ)
  where

  data binary-𝕎ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ) where
    make-binary-𝕎ᵉ :
      (aᵉ : Aᵉ) → (Bᵉ aᵉ → binary-𝕎ᵉ) → (Cᵉ aᵉ → binary-𝕎ᵉ) → binary-𝕎ᵉ
```