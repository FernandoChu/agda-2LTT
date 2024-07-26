# Peano arithmetic

```agda
module elementary-number-theory.peano-arithmeticᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.negated-equalityᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Axioms

Weᵉ stateᵉ theᵉ Peanoᵉ axiomsᵉ in typeᵉ theory,ᵉ using theᵉ
[identityᵉ type](foundation-core.identity-types.mdᵉ) asᵉ equality,ᵉ andᵉ proveᵉ thatᵉ
theyᵉ holdᵉ forᵉ theᵉ
[naturalᵉ numbersᵉ `ℕ`](elementary-number-theory.natural-numbers.md).ᵉ

### Peano's 1st axiom

Thereᵉ isᵉ anᵉ elementᵉ **zero**ᵉ ofᵉ theᵉ naturalᵉ numbers.ᵉ

```agda
peano-axiom-1ᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
peano-axiom-1ᵉ Nᵉ = Nᵉ

peano-1-ℕᵉ : peano-axiom-1ᵉ ℕᵉ
peano-1-ℕᵉ = zero-ℕᵉ
```

## Peano's 2nd axiom

Theᵉ identityᵉ relationᵉ onᵉ theᵉ naturalᵉ numbersᵉ isᵉ reflexive.ᵉ I.e.ᵉ forᵉ everyᵉ
naturalᵉ numberᵉ `x`,ᵉ itᵉ isᵉ trueᵉ thatᵉ `xᵉ ＝ᵉ x`.ᵉ

```agda
peano-axiom-2ᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
peano-axiom-2ᵉ Nᵉ = (xᵉ : Nᵉ) → xᵉ ＝ᵉ xᵉ

peano-2-ℕᵉ : peano-axiom-2ᵉ ℕᵉ
peano-2-ℕᵉ xᵉ = reflᵉ
```

### Peano's 3rd axiom

Theᵉ identityᵉ relationᵉ onᵉ theᵉ naturalᵉ numbersᵉ isᵉ symmetric.ᵉ I.e.ᵉ ifᵉ `xᵉ ＝ᵉ y`,ᵉ
thenᵉ `yᵉ ＝ᵉ x`.ᵉ

```agda
peano-axiom-3ᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
peano-axiom-3ᵉ Nᵉ = (xᵉ yᵉ : Nᵉ) → xᵉ ＝ᵉ yᵉ → yᵉ ＝ᵉ xᵉ

peano-3-ℕᵉ : peano-axiom-3ᵉ ℕᵉ
peano-3-ℕᵉ xᵉ yᵉ = invᵉ
```

### Peano's 4th axiom

Theᵉ identityᵉ relationᵉ onᵉ theᵉ naturalᵉ numbersᵉ isᵉ transitive.ᵉ I.e.ᵉ ifᵉ `yᵉ ＝ᵉ z`ᵉ andᵉ
`xᵉ ＝ᵉ y`,ᵉ thenᵉ `xᵉ ＝ᵉ z`.ᵉ

```agda
peano-axiom-4ᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
peano-axiom-4ᵉ Nᵉ = (xᵉ yᵉ zᵉ : Nᵉ) → yᵉ ＝ᵉ zᵉ → xᵉ ＝ᵉ yᵉ → xᵉ ＝ᵉ zᵉ

peano-4-ℕᵉ : peano-axiom-4ᵉ ℕᵉ
peano-4-ℕᵉ xᵉ yᵉ zᵉ = concat'ᵉ xᵉ
```

### Peano's 5th axiom

Theᵉ 5thᵉ axiomᵉ ofᵉ peano'sᵉ arithmeticᵉ statesᵉ thatᵉ forᵉ everyᵉ `x`ᵉ andᵉ `y`,ᵉ ifᵉ
`xᵉ ＝ᵉ y`ᵉ andᵉ `y`ᵉ isᵉ aᵉ naturalᵉ number,ᵉ thenᵉ `x`ᵉ isᵉ aᵉ naturalᵉ number.ᵉ Thisᵉ axiomᵉ
doesᵉ notᵉ makeᵉ senseᵉ in typeᵉ theory,ᵉ asᵉ everyᵉ elementᵉ byᵉ definitionᵉ livesᵉ in aᵉ
specifiedᵉ type.ᵉ Toᵉ evenᵉ poseᵉ theᵉ questionᵉ ofᵉ whetherᵉ twoᵉ elementsᵉ areᵉ equal,ᵉ weᵉ
mustᵉ alreadyᵉ knowᵉ thatᵉ theyᵉ areᵉ elementsᵉ ofᵉ theᵉ sameᵉ type.ᵉ

### Peano's 6th axiom

Forᵉ everyᵉ naturalᵉ number,ᵉ thereᵉ isᵉ aᵉ **successor**ᵉ naturalᵉ number.ᵉ

```agda
peano-axiom-6ᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
peano-axiom-6ᵉ Nᵉ = Nᵉ → Nᵉ

peano-6-ℕᵉ : peano-axiom-6ᵉ ℕᵉ
peano-6-ℕᵉ = succ-ℕᵉ
```

### Peano's 7th axiom

Forᵉ twoᵉ naturalᵉ numbersᵉ `x`ᵉ andᵉ `y`,ᵉ ifᵉ theᵉ successorᵉ ofᵉ `x`ᵉ isᵉ identifiedᵉ with
theᵉ successorᵉ ofᵉ `y`,ᵉ thenᵉ `x`ᵉ isᵉ identifiedᵉ with `y`.ᵉ

```agda
peano-axiom-7ᵉ : {lᵉ : Level} (Nᵉ : UUᵉ lᵉ) → peano-axiom-6ᵉ Nᵉ → UUᵉ lᵉ
peano-axiom-7ᵉ Nᵉ succᵉ = (xᵉ yᵉ : Nᵉ) → (xᵉ ＝ᵉ yᵉ) ↔ᵉ (succᵉ xᵉ ＝ᵉ succᵉ yᵉ)

peano-7-ℕᵉ : peano-axiom-7ᵉ ℕᵉ peano-6-ℕᵉ
pr1ᵉ (peano-7-ℕᵉ xᵉ yᵉ) reflᵉ = reflᵉ
pr2ᵉ (peano-7-ℕᵉ xᵉ yᵉ) = is-injective-succ-ℕᵉ
```

### Peano's 8th axiom

Theᵉ zeroᵉ naturalᵉ numberᵉ mayᵉ notᵉ beᵉ identifiedᵉ with anyᵉ successorᵉ naturalᵉ number.ᵉ

```agda
peano-axiom-8ᵉ :
  {lᵉ : Level} (Nᵉ : UUᵉ lᵉ) → peano-axiom-1ᵉ Nᵉ → peano-axiom-6ᵉ Nᵉ → UUᵉ lᵉ
peano-axiom-8ᵉ Nᵉ zeroᵉ succᵉ = (xᵉ : Nᵉ) → succᵉ xᵉ ≠ᵉ zeroᵉ

peano-8-ℕᵉ : peano-axiom-8ᵉ ℕᵉ peano-1-ℕᵉ peano-6-ℕᵉ
peano-8-ℕᵉ = is-nonzero-succ-ℕᵉ
```

### Peano's 9th axiom

Theᵉ naturalᵉ numbersᵉ satisfyᵉ theᵉ followingᵉ
[propositional](foundation-core.propositions.mdᵉ) inductionᵉ principleᵉ:

Givenᵉ aᵉ predicateᵉ onᵉ theᵉ naturalᵉ numbersᵉ `Pᵉ : Nᵉ → Prop`,ᵉ ifᵉ

-ᵉ `Pᵉ zero`ᵉ holds,ᵉ

andᵉ

-ᵉ ifᵉ `Pᵉ x`ᵉ holdsᵉ thenᵉ `Pᵉ (succᵉ x)`ᵉ holds,ᵉ

thenᵉ `Pᵉ x`ᵉ holdsᵉ forᵉ allᵉ naturalᵉ numbersᵉ `x`.ᵉ

```agda
peano-axiom-9ᵉ :
  {lᵉ : Level} (Nᵉ : UUᵉ lᵉ) → peano-axiom-1ᵉ Nᵉ → peano-axiom-6ᵉ Nᵉ → UUωᵉ
peano-axiom-9ᵉ Nᵉ zeroᵉ succᵉ =
  {l'ᵉ : Level} (Pᵉ : Nᵉ → Propᵉ l'ᵉ) →
  type-Propᵉ (Pᵉ zeroᵉ) →
  ((xᵉ : Nᵉ) → type-Propᵉ (Pᵉ xᵉ) → type-Propᵉ (Pᵉ (succᵉ xᵉ))) →
  ((xᵉ : Nᵉ) → type-Propᵉ (Pᵉ xᵉ))

peano-9-ℕᵉ : peano-axiom-9ᵉ ℕᵉ peano-1-ℕᵉ peano-6-ℕᵉ
peano-9-ℕᵉ Pᵉ = ind-ℕᵉ {Pᵉ = type-Propᵉ ∘ᵉ Pᵉ}
```

## External links

-ᵉ [Peanoᵉ arithmetic](https://ncatlab.org/nlab/show/Peano+arithmeticᵉ) atᵉ $n$Labᵉ
-ᵉ [Peanoᵉ axioms](https://www.wikidata.org/wiki/Q842755ᵉ) atᵉ Wikidataᵉ
-ᵉ [Peanoᵉ axioms](https://www.britannica.com/science/Peano-axiomsᵉ) atᵉ Britannicaᵉ
-ᵉ [Peanoᵉ axioms](https://en.wikipedia.org/wiki/Peano_axiomsᵉ) atᵉ Wikipediaᵉ
-ᵉ [Peano'sᵉ Axioms](https://mathworld.wolfram.com/PeanosAxioms.htmlᵉ) atᵉ Wolframᵉ
  Mathworldᵉ