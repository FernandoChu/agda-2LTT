# Trivial commutative rings

```agda
module commutative-algebra.trivial-commutative-ringsᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-ringsᵉ
open import commutative-algebra.isomorphisms-commutative-ringsᵉ

open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.negationᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.identity-typesᵉ

open import group-theory.abelian-groupsᵉ
open import group-theory.trivial-groupsᵉ

open import ring-theory.ringsᵉ
open import ring-theory.trivial-ringsᵉ
```

</details>

## Idea

**Trivialᵉ commutativeᵉ rings**ᵉ areᵉ commutativeᵉ ringsᵉ in whichᵉ `0ᵉ = 1`.ᵉ

## Definition

```agda
is-trivial-commutative-ring-Propᵉ :
  {lᵉ : Level} → Commutative-Ringᵉ lᵉ → Propᵉ lᵉ
is-trivial-commutative-ring-Propᵉ Aᵉ =
  Id-Propᵉ
    ( set-Commutative-Ringᵉ Aᵉ)
    ( zero-Commutative-Ringᵉ Aᵉ)
    ( one-Commutative-Ringᵉ Aᵉ)

is-trivial-Commutative-Ringᵉ :
  {lᵉ : Level} → Commutative-Ringᵉ lᵉ → UUᵉ lᵉ
is-trivial-Commutative-Ringᵉ Aᵉ =
  type-Propᵉ (is-trivial-commutative-ring-Propᵉ Aᵉ)

is-prop-is-trivial-Commutative-Ringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) →
  is-propᵉ (is-trivial-Commutative-Ringᵉ Aᵉ)
is-prop-is-trivial-Commutative-Ringᵉ Aᵉ =
  is-prop-type-Propᵉ (is-trivial-commutative-ring-Propᵉ Aᵉ)

is-nontrivial-commutative-ring-Propᵉ :
  {lᵉ : Level} → Commutative-Ringᵉ lᵉ → Propᵉ lᵉ
is-nontrivial-commutative-ring-Propᵉ Aᵉ =
  neg-Propᵉ (is-trivial-commutative-ring-Propᵉ Aᵉ)

is-nontrivial-Commutative-Ringᵉ :
  {lᵉ : Level} → Commutative-Ringᵉ lᵉ → UUᵉ lᵉ
is-nontrivial-Commutative-Ringᵉ Aᵉ =
  type-Propᵉ (is-nontrivial-commutative-ring-Propᵉ Aᵉ)

is-prop-is-nontrivial-Commutative-Ringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) →
  is-propᵉ (is-nontrivial-Commutative-Ringᵉ Aᵉ)
is-prop-is-nontrivial-Commutative-Ringᵉ Aᵉ =
  is-prop-type-Propᵉ (is-nontrivial-commutative-ring-Propᵉ Aᵉ)
```

## Properties

### The carrier type of a zero commutative ring is contractible

```agda
is-contr-is-trivial-Commutative-Ringᵉ :
  {lᵉ : Level} (Aᵉ : Commutative-Ringᵉ lᵉ) →
  is-trivial-Commutative-Ringᵉ Aᵉ →
  is-contrᵉ (type-Commutative-Ringᵉ Aᵉ)
is-contr-is-trivial-Commutative-Ringᵉ Aᵉ pᵉ =
  is-contr-is-trivial-Ringᵉ (ring-Commutative-Ringᵉ Aᵉ) pᵉ
```

### The trivial ring

```agda
trivial-Ringᵉ : Ringᵉ lzero
pr1ᵉ trivial-Ringᵉ = trivial-Abᵉ
pr1ᵉ (pr1ᵉ (pr2ᵉ trivial-Ringᵉ)) xᵉ yᵉ = starᵉ
pr2ᵉ (pr1ᵉ (pr2ᵉ trivial-Ringᵉ)) xᵉ yᵉ zᵉ = reflᵉ
pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ trivial-Ringᵉ))) = starᵉ
pr1ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ trivial-Ringᵉ)))) starᵉ = reflᵉ
pr2ᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ trivial-Ringᵉ)))) starᵉ = reflᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ trivial-Ringᵉ)) = (λ aᵉ bᵉ cᵉ → reflᵉ) ,ᵉ (λ aᵉ bᵉ cᵉ → reflᵉ)

is-commutative-trivial-Ringᵉ : is-commutative-Ringᵉ trivial-Ringᵉ
is-commutative-trivial-Ringᵉ xᵉ yᵉ = reflᵉ

trivial-Commutative-Ringᵉ : Commutative-Ringᵉ lzero
trivial-Commutative-Ringᵉ = (trivial-Ringᵉ ,ᵉ is-commutative-trivial-Ringᵉ)

is-trivial-trivial-Commutative-Ringᵉ :
  is-trivial-Commutative-Ringᵉ trivial-Commutative-Ringᵉ
is-trivial-trivial-Commutative-Ringᵉ = reflᵉ
```

### The type of trivial rings is contractible

To-doᵉ: completeᵉ proofᵉ ofᵉ uniquenessᵉ ofᵉ theᵉ zeroᵉ ringᵉ using SIP,ᵉ ideallyᵉ refactorᵉ
codeᵉ to do zeroᵉ algebrasᵉ allᵉ alongᵉ theᵉ chainᵉ to prettifyᵉ andᵉ streamlineᵉ futureᵉ
workᵉ