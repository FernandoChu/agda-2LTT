# Boolean reflection

```agda
module reflection.boolean-reflectionᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleansᵉ
open import foundation.decidable-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.coproduct-typesᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Theᵉ ideaᵉ ofᵉ booleanᵉ reflectionᵉ isᵉ to useᵉ theᵉ equalityᵉ checkerᵉ ofᵉ theᵉ proofᵉ
assistantᵉ in orderᵉ to offloadᵉ proofᵉ obligationsᵉ to theᵉ computer.ᵉ Thisᵉ worksᵉ in
twoᵉ steps.ᵉ First,ᵉ weᵉ constructᵉ theᵉ booleanization,ᵉ whichᵉ isᵉ aᵉ mapᵉ
`is-decidableᵉ Aᵉ → bool`,ᵉ thatᵉ sendsᵉ elementsᵉ ofᵉ theᵉ formᵉ `inlᵉ a`ᵉ to `true`ᵉ andᵉ
elementsᵉ ofᵉ theᵉ formᵉ `inrᵉ na`ᵉ to `false`.ᵉ Thenᵉ weᵉ constructᵉ theᵉ booleanᵉ
reflectionᵉ function,ᵉ whichᵉ takesᵉ aᵉ decisionᵉ `dᵉ : is-decidableᵉ A`ᵉ andᵉ anᵉ
identificationᵉ `Idᵉ (booleanizationᵉ dᵉ) true`ᵉ to anᵉ elementᵉ ofᵉ `A`.ᵉ Thisᵉ allowsᵉ usᵉ
to constructᵉ anᵉ elementᵉ ofᵉ `A`ᵉ ifᵉ itᵉ hasᵉ elements,ᵉ byᵉ
`boolean-reflectionᵉ dᵉ refl`.ᵉ Indeed,ᵉ ifᵉ `A`ᵉ wasᵉ nonempty,ᵉ thenᵉ theᵉ decisionᵉ
`dᵉ : is-decidableᵉ A`ᵉ mustᵉ haveᵉ beenᵉ ofᵉ theᵉ formᵉ `inlᵉ a`ᵉ forᵉ someᵉ elementᵉ `a`,ᵉ
andᵉ thatᵉ `refl`ᵉ isᵉ indeedᵉ anᵉ identificationᵉ `Idᵉ (booleanizationᵉ dᵉ) true`.ᵉ

## Definition

```agda
booleanizationᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-decidableᵉ Aᵉ → boolᵉ
booleanizationᵉ (inlᵉ aᵉ) = trueᵉ
booleanizationᵉ (inrᵉ fᵉ) = falseᵉ

inv-boolean-reflectionᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (dᵉ : is-decidableᵉ Aᵉ) → Aᵉ → booleanizationᵉ dᵉ ＝ᵉ trueᵉ
inv-boolean-reflectionᵉ (inlᵉ aᵉ) xᵉ = reflᵉ
inv-boolean-reflectionᵉ (inrᵉ fᵉ) xᵉ = ex-falsoᵉ (fᵉ xᵉ)

boolean-reflectionᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (dᵉ : is-decidableᵉ Aᵉ) → booleanizationᵉ dᵉ ＝ᵉ trueᵉ → Aᵉ
boolean-reflectionᵉ (inlᵉ aᵉ) pᵉ = aᵉ
boolean-reflectionᵉ (inrᵉ fᵉ) pᵉ = ex-falsoᵉ (Eq-eq-boolᵉ pᵉ)
```