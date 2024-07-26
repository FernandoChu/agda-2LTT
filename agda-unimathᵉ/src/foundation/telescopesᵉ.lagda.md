# Telescopes

```agda
module foundation.telescopesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.universe-levelsᵉ
```

</details>

## Idea

Aᵉ **telescope**,ᵉ orᵉ **iteratedᵉ typeᵉ family**,ᵉ isᵉ aᵉ listᵉ ofᵉ typeᵉ familiesᵉ
`(A₀,ᵉ A₁,ᵉ A₂,ᵉ ...,ᵉ A_n)`ᵉ consistingᵉ ofᵉ

-ᵉ aᵉ typeᵉ `A₀`,ᵉ
-ᵉ aᵉ typeᵉ familyᵉ `A₁ᵉ : A₀ᵉ → 𝒰`,ᵉ
-ᵉ aᵉ typeᵉ familyᵉ `A₂ᵉ : (x₀ᵉ : A₀ᵉ) → A₁ᵉ x₀ᵉ → 𝒰`,ᵉ
-ᵉ ...
-ᵉ aᵉ typeᵉ familyᵉ `A_nᵉ : (x₀ᵉ : A₀ᵉ) ... (x_(n-1ᵉ) : A_(n-1ᵉ) x₀ᵉ ... x_(n-2ᵉ)) → 𝒰`.ᵉ

Weᵉ sayᵉ thatᵉ aᵉ telescopeᵉ `(A₀,...,A_n)`ᵉ hasᵉ **length**ᵉ `n+1`.ᵉ Inᵉ otherᵉ words,ᵉ theᵉ
lengthᵉ ofᵉ theᵉ telescopeᵉ `(A₀,...,A_n)`ᵉ isᵉ theᵉ lengthᵉ ofᵉ theᵉ (dependentᵉ) listᵉ
`(A₀,...,A_n)`.ᵉ

Weᵉ encodeᵉ theᵉ typeᵉ ofᵉ telescopesᵉ asᵉ aᵉ familyᵉ ofᵉ inductive typesᵉ

```text
  telescopeᵉ : (lᵉ : Level) → ℕᵉ → UUωᵉ
```

Theᵉ typeᵉ ofᵉ telescopesᵉ isᵉ aᵉ [directedᵉ tree](trees.directed-trees.mdᵉ)

```text
  ... → T₃ᵉ → T₂ᵉ → T₁ᵉ → T₀,ᵉ
```

where `T_n`ᵉ isᵉ theᵉ typeᵉ ofᵉ allᵉ telescopesᵉ ofᵉ lengthᵉ `n`,ᵉ andᵉ theᵉ mapᵉ fromᵉ
`T_(n+1)`ᵉ to `T_n`ᵉ mapsᵉ `(A₀,...,A_n)`ᵉ to `(A₀,...,A_(n-1))`.ᵉ Theᵉ typeᵉ ofᵉ suchᵉ
directedᵉ treesᵉ canᵉ beᵉ definedᵉ asᵉ aᵉ coinductiveᵉ record type,ᵉ andᵉ weᵉ willᵉ defineᵉ
theᵉ treeᵉ `T`ᵉ ofᵉ telescopesᵉ asᵉ aᵉ particularᵉ elementᵉ ofᵉ thisᵉ tree.ᵉ

## Definitions

### Telescopes

```agda
data
  telescopeᵉ : (lᵉ : Level) → ℕᵉ → UUωᵉ
  where
  base-telescopeᵉ :
    {l1ᵉ : Level} → UUᵉ l1ᵉ → telescopeᵉ l1ᵉ zero-ℕᵉ
  cons-telescopeᵉ :
    {l1ᵉ l2ᵉ : Level} {nᵉ : ℕᵉ} {Xᵉ : UUᵉ l1ᵉ} →
    (Xᵉ → telescopeᵉ l2ᵉ nᵉ) → telescopeᵉ (l1ᵉ ⊔ l2ᵉ) (succ-ℕᵉ nᵉ)

open telescopeᵉ public
```

Aᵉ veryᵉ slightᵉ reformulationᵉ ofᵉ `cons-telescope`ᵉ forᵉ convenienceᵉ:

```agda
prepend-telescopeᵉ :
  {l1ᵉ l2ᵉ : Level} {nᵉ : ℕᵉ} →
  (Aᵉ : UUᵉ l1ᵉ) → ({xᵉ : Aᵉ} → telescopeᵉ l2ᵉ nᵉ) → telescopeᵉ (l1ᵉ ⊔ l2ᵉ) (succ-ℕᵉ nᵉ)
prepend-telescopeᵉ Aᵉ Bᵉ = cons-telescopeᵉ {Xᵉ = Aᵉ} (λ xᵉ → Bᵉ {xᵉ})
```

### Telescopes at a universe level

Oneᵉ issueᵉ with theᵉ previousᵉ definitionᵉ ofᵉ telescopesᵉ isᵉ thatᵉ itᵉ isᵉ impossibleᵉ to
extractᵉ anyᵉ typeᵉ informationᵉ fromᵉ it.ᵉ Atᵉ theᵉ expenseᵉ ofᵉ givingᵉ upᵉ fullᵉ universeᵉ
polymorphism,ᵉ weᵉ canᵉ defineᵉ aᵉ notionᵉ ofᵉ **telescopesᵉ atᵉ aᵉ universeᵉ level**ᵉ thatᵉ
admitsᵉ suchᵉ projections.ᵉ Thisᵉ definitionᵉ isᵉ alsoᵉ compatibleᵉ with theᵉ
`--level-universe`ᵉ restriction.ᵉ

```agda
data telescope-Levelᵉ (lᵉ : Level) : ℕᵉ → UUᵉ (lsuc lᵉ)
  where
  base-telescope-Levelᵉ :
    UUᵉ lᵉ → telescope-Levelᵉ lᵉ zero-ℕᵉ
  cons-telescope-Levelᵉ :
    {nᵉ : ℕᵉ} {Xᵉ : UUᵉ lᵉ} →
    (Xᵉ → telescope-Levelᵉ lᵉ nᵉ) → telescope-Levelᵉ lᵉ (succ-ℕᵉ nᵉ)

open telescope-Levelᵉ public

telescope-telescope-Levelᵉ :
  {lᵉ : Level} {nᵉ : ℕᵉ} → telescope-Levelᵉ lᵉ nᵉ → telescopeᵉ lᵉ nᵉ
telescope-telescope-Levelᵉ (base-telescope-Levelᵉ Aᵉ) =
  base-telescopeᵉ Aᵉ
telescope-telescope-Levelᵉ (cons-telescope-Levelᵉ Γᵉ) =
  cons-telescopeᵉ (λ xᵉ → telescope-telescope-Levelᵉ (Γᵉ xᵉ))
```

### Transformations on telescopes

Givenᵉ anᵉ operationᵉ onᵉ universes,ᵉ weᵉ canᵉ applyᵉ itᵉ atᵉ theᵉ baseᵉ ofᵉ theᵉ telescope.ᵉ

```agda
apply-base-telescopeᵉ :
  {l1ᵉ : Level} {nᵉ : ℕᵉ}
  (Pᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ) → telescopeᵉ l1ᵉ nᵉ → telescopeᵉ l1ᵉ nᵉ
apply-base-telescopeᵉ Pᵉ (base-telescopeᵉ Aᵉ) = base-telescopeᵉ (Pᵉ Aᵉ)
apply-base-telescopeᵉ Pᵉ (cons-telescopeᵉ Aᵉ) =
  cons-telescopeᵉ (λ xᵉ → apply-base-telescopeᵉ Pᵉ (Aᵉ xᵉ))
```

### Telescopes as instance arguments

Toᵉ getᵉ Agdaᵉ to inferᵉ telescopes,ᵉ weᵉ helpᵉ itᵉ alongᵉ aᵉ littleᵉ using
[instanceᵉ arguments](https://agda.readthedocs.io/en/latest/language/instance-arguments.html).ᵉ
Theseᵉ areᵉ aᵉ specialᵉ kindᵉ ofᵉ implicitᵉ argumentᵉ in Agdaᵉ thatᵉ areᵉ resolvedᵉ byᵉ theᵉ
instance resolutionᵉ algorithm.ᵉ Weᵉ registerᵉ buildingᵉ blocksᵉ forᵉ thisᵉ algorithmᵉ to
useᵉ below,ᵉ i.e.ᵉ _instances_.ᵉ Thenᵉ Agdaᵉ willᵉ attemptᵉ to useᵉ thoseᵉ to constructᵉ
telescopesᵉ ofᵉ theᵉ appropriateᵉ kindᵉ whenᵉ askedᵉ to.ᵉ

Inᵉ theᵉ caseᵉ ofᵉ telescopes,ᵉ thisᵉ hasᵉ theᵉ unfortunateᵉ disadvantageᵉ thatᵉ weᵉ canᵉ
onlyᵉ defineᵉ instancesᵉ forᵉ fixedᵉ lengthᵉ telescopes.ᵉ Weᵉ haveᵉ definedᵉ instancesᵉ ofᵉ
telescopesᵉ upᵉ to lengthᵉ 18,ᵉ soᵉ althoughᵉ Agdaᵉ cannotᵉ inferᵉ aᵉ telescopeᵉ ofᵉ aᵉ
generalᵉ lengthᵉ using thisᵉ approach,ᵉ itᵉ canᵉ inferᵉ themᵉ upᵉ to thisᵉ givenᵉ length.ᵉ

```agda
instance-telescopeᵉ : {lᵉ : Level} {nᵉ : ℕᵉ} → {{telescopeᵉ lᵉ nᵉ}} → telescopeᵉ lᵉ nᵉ
instance-telescopeᵉ {{xᵉ}} = xᵉ

instance
  instance-telescope⁰ᵉ : {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → telescopeᵉ lᵉ zero-ℕᵉ
  instance-telescope⁰ᵉ {Xᵉ = Xᵉ} = base-telescopeᵉ Xᵉ

  instance-telescope¹ᵉ :
    { l1ᵉ lᵉ : Level} {A1ᵉ : UUᵉ l1ᵉ} {Xᵉ : A1ᵉ → UUᵉ lᵉ} → telescopeᵉ (l1ᵉ ⊔ lᵉ) 1ᵉ
  instance-telescope¹ᵉ {Xᵉ = Xᵉ} =
    cons-telescopeᵉ (λ xᵉ → instance-telescope⁰ᵉ {Xᵉ = Xᵉ xᵉ})

  instance-telescope²ᵉ :
    { l1ᵉ l2ᵉ lᵉ : Level} {A1ᵉ : UUᵉ l1ᵉ} {A2ᵉ : A1ᵉ → UUᵉ l2ᵉ}
    { Xᵉ : (x1ᵉ : A1ᵉ) → A2ᵉ x1ᵉ → UUᵉ lᵉ} → telescopeᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lᵉ) 2ᵉ
  instance-telescope²ᵉ {Xᵉ = Xᵉ} =
    cons-telescopeᵉ (λ xᵉ → instance-telescope¹ᵉ {Xᵉ = Xᵉ xᵉ})

  instance-telescope³ᵉ :
    { l1ᵉ l2ᵉ l3ᵉ lᵉ : Level}
    { A1ᵉ : UUᵉ l1ᵉ} {A2ᵉ : A1ᵉ → UUᵉ l2ᵉ} {A3ᵉ : (x1ᵉ : A1ᵉ) → A2ᵉ x1ᵉ → UUᵉ l3ᵉ}
    { Xᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x2ᵉ : A3ᵉ x1ᵉ x2ᵉ) → UUᵉ lᵉ} →
    telescopeᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ lᵉ) 3ᵉ
  instance-telescope³ᵉ {Xᵉ = Xᵉ} =
    cons-telescopeᵉ (λ xᵉ → instance-telescope²ᵉ {Xᵉ = Xᵉ xᵉ})

  instance-telescope⁴ᵉ :
    { l1ᵉ l2ᵉ l3ᵉ l4ᵉ lᵉ : Level}
    { A1ᵉ : UUᵉ l1ᵉ} {A2ᵉ : A1ᵉ → UUᵉ l2ᵉ} {A3ᵉ : (x1ᵉ : A1ᵉ) → A2ᵉ x1ᵉ → UUᵉ l3ᵉ}
    { A4ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) → A3ᵉ x1ᵉ x2ᵉ → UUᵉ l4ᵉ}
    { Xᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ) → UUᵉ lᵉ} →
    telescopeᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ lᵉ) 4ᵉ
  instance-telescope⁴ᵉ {Xᵉ = Xᵉ} =
    cons-telescopeᵉ (λ xᵉ → instance-telescope³ᵉ {Xᵉ = Xᵉ xᵉ})

  instance-telescope⁵ᵉ :
    { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ lᵉ : Level}
    { A1ᵉ : UUᵉ l1ᵉ} {A2ᵉ : A1ᵉ → UUᵉ l2ᵉ} {A3ᵉ : (x1ᵉ : A1ᵉ) → A2ᵉ x1ᵉ → UUᵉ l3ᵉ}
    { A4ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) → A3ᵉ x1ᵉ x2ᵉ → UUᵉ l4ᵉ}
    { A5ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ) → UUᵉ l5ᵉ}
    { Xᵉ :
      (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
      (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) → UUᵉ lᵉ} →
    telescopeᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ lᵉ) 5ᵉ
  instance-telescope⁵ᵉ {Xᵉ = Xᵉ} =
    cons-telescopeᵉ (λ xᵉ → instance-telescope⁴ᵉ {Xᵉ = Xᵉ xᵉ})

--   instance-telescope⁶ᵉ :
--     { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ lᵉ : Level}
--     { A1ᵉ : UUᵉ l1ᵉ} {A2ᵉ : A1ᵉ → UUᵉ l2ᵉ} {A3ᵉ : (x1ᵉ : A1ᵉ) → A2ᵉ x1ᵉ → UUᵉ l3ᵉ}
--     { A4ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) → A3ᵉ x1ᵉ x2ᵉ → UUᵉ l4ᵉ}
--     { A5ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ) → UUᵉ l5ᵉ}
--     { A6ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) → UUᵉ l6ᵉ}
--     { Xᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ) → UUᵉ lᵉ} →
--     telescopeᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ lᵉ) 6
--   instance-telescope⁶ᵉ {Xᵉ = Xᵉ} =
--     cons-telescopeᵉ (λ xᵉ → instance-telescope⁵ᵉ {Xᵉ = Xᵉ xᵉ})

--   instance-telescope⁷ᵉ :
--     { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ lᵉ : Level}
--     { A1ᵉ : UUᵉ l1ᵉ} {A2ᵉ : A1ᵉ → UUᵉ l2ᵉ} {A3ᵉ : (x1ᵉ : A1ᵉ) → A2ᵉ x1ᵉ → UUᵉ l3ᵉ}
--     { A4ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) → A3ᵉ x1ᵉ x2ᵉ → UUᵉ l4ᵉ}
--     { A5ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ) → UUᵉ l5ᵉ}
--     { A6ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) → UUᵉ l6ᵉ}
--     { A7ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ) → UUᵉ l7ᵉ}
--     { Xᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) → UUᵉ lᵉ} →
--     telescopeᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l7ᵉ ⊔ lᵉ) 7
--   instance-telescope⁷ᵉ {Xᵉ = Xᵉ} =
--     cons-telescopeᵉ (λ xᵉ → instance-telescope⁶ᵉ {Xᵉ = Xᵉ xᵉ})

--   instance-telescope⁸ᵉ :
--     { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ lᵉ : Level}
--     { A1ᵉ : UUᵉ l1ᵉ} {A2ᵉ : A1ᵉ → UUᵉ l2ᵉ} {A3ᵉ : (x1ᵉ : A1ᵉ) → A2ᵉ x1ᵉ → UUᵉ l3ᵉ}
--     { A4ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) → A3ᵉ x1ᵉ x2ᵉ → UUᵉ l4ᵉ}
--     { A5ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ) → UUᵉ l5ᵉ}
--     { A6ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) → UUᵉ l6ᵉ}
--     { A7ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ) → UUᵉ l7ᵉ}
--     { A8ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) → UUᵉ l8ᵉ}
--     { Xᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ) → UUᵉ lᵉ} →
--     telescopeᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l7ᵉ ⊔ l8ᵉ ⊔ lᵉ) 8
--   instance-telescope⁸ᵉ {Xᵉ = Xᵉ} =
--     cons-telescopeᵉ (λ xᵉ → instance-telescope⁷ᵉ {Xᵉ = Xᵉ xᵉ})

--   instance-telescope⁹ᵉ :
--     { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ lᵉ : Level}
--     { A1ᵉ : UUᵉ l1ᵉ} {A2ᵉ : A1ᵉ → UUᵉ l2ᵉ} {A3ᵉ : (x1ᵉ : A1ᵉ) → A2ᵉ x1ᵉ → UUᵉ l3ᵉ}
--     { A4ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) → A3ᵉ x1ᵉ x2ᵉ → UUᵉ l4ᵉ}
--     { A5ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ) → UUᵉ l5ᵉ}
--     { A6ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) → UUᵉ l6ᵉ}
--     { A7ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ) → UUᵉ l7ᵉ}
--     { A8ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) → UUᵉ l8ᵉ}
--     { A9ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ) →
--       UUᵉ l9ᵉ}
--     { Xᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) → UUᵉ lᵉ} →
--     telescopeᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l7ᵉ ⊔ l8ᵉ ⊔ l9ᵉ ⊔ lᵉ) 9
--   instance-telescope⁹ᵉ {Xᵉ = Xᵉ} =
--     cons-telescopeᵉ (λ xᵉ → instance-telescope⁸ᵉ {Xᵉ = Xᵉ xᵉ})

--   instance-telescope¹⁰ᵉ :
--     { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ l10ᵉ lᵉ : Level}
--     { A1ᵉ : UUᵉ l1ᵉ} {A2ᵉ : A1ᵉ → UUᵉ l2ᵉ} {A3ᵉ : (x1ᵉ : A1ᵉ) → A2ᵉ x1ᵉ → UUᵉ l3ᵉ}
--     { A4ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) → A3ᵉ x1ᵉ x2ᵉ → UUᵉ l4ᵉ}
--     { A5ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ) → UUᵉ l5ᵉ}
--     { A6ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) → UUᵉ l6ᵉ}
--     { A7ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ) → UUᵉ l7ᵉ}
--     { A8ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) → UUᵉ l8ᵉ}
--     { A9ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ) →
--       UUᵉ l9ᵉ}
--     { A10ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) →
--       UUᵉ l10ᵉ}
--     { Xᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ) →
--       UUᵉ lᵉ} →
--     telescopeᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l7ᵉ ⊔ l8ᵉ ⊔ l9ᵉ ⊔ l10ᵉ ⊔ lᵉ) 10
--   instance-telescope¹⁰ᵉ {Xᵉ = Xᵉ} =
--     cons-telescopeᵉ (λ xᵉ → instance-telescope⁹ᵉ {Xᵉ = Xᵉ xᵉ})

--   instance-telescope¹¹ᵉ :
--     { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ l10ᵉ l11ᵉ lᵉ : Level}
--     { A1ᵉ : UUᵉ l1ᵉ} {A2ᵉ : A1ᵉ → UUᵉ l2ᵉ} {A3ᵉ : (x1ᵉ : A1ᵉ) → A2ᵉ x1ᵉ → UUᵉ l3ᵉ}
--     { A4ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) → A3ᵉ x1ᵉ x2ᵉ → UUᵉ l4ᵉ}
--     { A5ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ) → UUᵉ l5ᵉ}
--     { A6ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) → UUᵉ l6ᵉ}
--     { A7ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ) → UUᵉ l7ᵉ}
--     { A8ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) → UUᵉ l8ᵉ}
--     { A9ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ) →
--       UUᵉ l9ᵉ}
--     { A10ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) →
--       UUᵉ l10ᵉ}
--     { A11ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ) →
--       UUᵉ l11ᵉ}
--     { Xᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ) → UUᵉ lᵉ} →
--     telescopeᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l7ᵉ ⊔ l8ᵉ ⊔ l9ᵉ ⊔ l10ᵉ ⊔ l11ᵉ ⊔ lᵉ) 11
--   instance-telescope¹¹ᵉ {Xᵉ = Xᵉ} =
--     cons-telescopeᵉ (λ xᵉ → instance-telescope¹⁰ᵉ {Xᵉ = Xᵉ xᵉ})

--   instance-telescope¹²ᵉ :
--     { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ l10ᵉ l11ᵉ l12ᵉ lᵉ : Level}
--     { A1ᵉ : UUᵉ l1ᵉ} {A2ᵉ : A1ᵉ → UUᵉ l2ᵉ} {A3ᵉ : (x1ᵉ : A1ᵉ) → A2ᵉ x1ᵉ → UUᵉ l3ᵉ}
--     { A4ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) → A3ᵉ x1ᵉ x2ᵉ → UUᵉ l4ᵉ}
--     { A5ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ) → UUᵉ l5ᵉ}
--     { A6ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) → UUᵉ l6ᵉ}
--     { A7ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ) → UUᵉ l7ᵉ}
--     { A8ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) → UUᵉ l8ᵉ}
--     { A9ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ) →
--       UUᵉ l9ᵉ}
--     { A10ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) →
--       UUᵉ l10ᵉ}
--     { A11ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ) →
--       UUᵉ l11ᵉ}
--     { A12ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ) → UUᵉ l12ᵉ}
--     { Xᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ) → UUᵉ lᵉ} →
--     telescopeᵉ
--       ( l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l7ᵉ ⊔ l8ᵉ ⊔ l9ᵉ ⊔ l10ᵉ ⊔ l11ᵉ ⊔ l12ᵉ ⊔ lᵉ)
--       ( 12ᵉ)
--   instance-telescope¹²ᵉ {Xᵉ = Xᵉ} =
--     cons-telescopeᵉ (λ xᵉ → instance-telescope¹¹ᵉ {Xᵉ = Xᵉ xᵉ})

--   instance-telescope¹³ᵉ :
--     { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ l10ᵉ l11ᵉ l12ᵉ l13ᵉ lᵉ : Level}
--     { A1ᵉ : UUᵉ l1ᵉ} {A2ᵉ : A1ᵉ → UUᵉ l2ᵉ} {A3ᵉ : (x1ᵉ : A1ᵉ) → A2ᵉ x1ᵉ → UUᵉ l3ᵉ}
--     { A4ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) → A3ᵉ x1ᵉ x2ᵉ → UUᵉ l4ᵉ}
--     { A5ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ) → UUᵉ l5ᵉ}
--     { A6ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) → UUᵉ l6ᵉ}
--     { A7ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ) → UUᵉ l7ᵉ}
--     { A8ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) → UUᵉ l8ᵉ}
--     { A9ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ) →
--       UUᵉ l9ᵉ}
--     { A10ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) →
--       UUᵉ l10ᵉ}
--     { A11ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ) →
--       UUᵉ l11ᵉ}
--     { A12ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ) → UUᵉ l12ᵉ}
--     { A13ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ) → UUᵉ l13ᵉ}
--     { Xᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ)
--       (x13ᵉ : A13ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ) → UUᵉ lᵉ} →
--     telescopeᵉ
--       ( l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l7ᵉ ⊔ l8ᵉ ⊔ l9ᵉ ⊔ l10ᵉ ⊔ l11ᵉ ⊔ l12ᵉ ⊔ l13ᵉ ⊔ lᵉ)
--       ( 13ᵉ)
--   instance-telescope¹³ᵉ {Xᵉ = Xᵉ} =
--     cons-telescopeᵉ (λ xᵉ → instance-telescope¹²ᵉ {Xᵉ = Xᵉ xᵉ})

--   instance-telescope¹⁴ᵉ :
--     { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ l10ᵉ l11ᵉ l12ᵉ l13ᵉ l14ᵉ lᵉ : Level}
--     { A1ᵉ : UUᵉ l1ᵉ} {A2ᵉ : A1ᵉ → UUᵉ l2ᵉ} {A3ᵉ : (x1ᵉ : A1ᵉ) → A2ᵉ x1ᵉ → UUᵉ l3ᵉ}
--     { A4ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) → A3ᵉ x1ᵉ x2ᵉ → UUᵉ l4ᵉ}
--     { A5ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ) → UUᵉ l5ᵉ}
--     { A6ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) → UUᵉ l6ᵉ}
--     { A7ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ) → UUᵉ l7ᵉ}
--     { A8ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) → UUᵉ l8ᵉ}
--     { A9ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ) →
--       UUᵉ l9ᵉ}
--     { A10ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) →
--       UUᵉ l10ᵉ}
--     { A11ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ) →
--       UUᵉ l11ᵉ}
--     { A12ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ) → UUᵉ l12ᵉ}
--     { A13ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ) → UUᵉ l13ᵉ}
--     { A14ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ)
--       (x13ᵉ : A13ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ) → UUᵉ l14ᵉ}
--     { Xᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ)
--       (x13ᵉ : A13ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ)
--       (x14ᵉ : A14ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ) → UUᵉ lᵉ} →
--     telescopeᵉ
--       ( l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l7ᵉ ⊔ l8ᵉ ⊔ l9ᵉ ⊔ l10ᵉ ⊔ l11ᵉ ⊔ l12ᵉ ⊔ l13ᵉ ⊔
--         l14ᵉ ⊔ lᵉ)
--       ( 14ᵉ)
--   instance-telescope¹⁴ᵉ {Xᵉ = Xᵉ} =
--     cons-telescopeᵉ (λ xᵉ → instance-telescope¹³ᵉ {Xᵉ = Xᵉ xᵉ})

--   instance-telescope¹⁵ᵉ :
--     { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ l10ᵉ l11ᵉ l12ᵉ l13ᵉ l14ᵉ l15ᵉ lᵉ : Level}
--     { A1ᵉ : UUᵉ l1ᵉ} {A2ᵉ : A1ᵉ → UUᵉ l2ᵉ} {A3ᵉ : (x1ᵉ : A1ᵉ) → A2ᵉ x1ᵉ → UUᵉ l3ᵉ}
--     { A4ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) → A3ᵉ x1ᵉ x2ᵉ → UUᵉ l4ᵉ}
--     { A5ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ) → UUᵉ l5ᵉ}
--     { A6ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) → UUᵉ l6ᵉ}
--     { A7ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ) → UUᵉ l7ᵉ}
--     { A8ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) → UUᵉ l8ᵉ}
--     { A9ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ) →
--       UUᵉ l9ᵉ}
--     { A10ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) →
--       UUᵉ l10ᵉ}
--     { A11ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ) →
--       UUᵉ l11ᵉ}
--     { A12ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ) → UUᵉ l12ᵉ}
--     { A13ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ) → UUᵉ l13ᵉ}
--     { A14ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ)
--       (x13ᵉ : A13ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ) → UUᵉ l14ᵉ}
--     { A15ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ)
--       (x13ᵉ : A13ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ)
--       (x14ᵉ : A14ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ) → UUᵉ l15ᵉ}
--     { Xᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ)
--       (x13ᵉ : A13ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ)
--       (x14ᵉ : A14ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ)
--       (x15ᵉ : A15ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ x14ᵉ) → UUᵉ lᵉ} →
--     telescopeᵉ
--       ( l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l7ᵉ ⊔ l8ᵉ ⊔ l9ᵉ ⊔ l10ᵉ ⊔ l11ᵉ ⊔ l12ᵉ ⊔ l13ᵉ ⊔
--         l14ᵉ ⊔ l15ᵉ ⊔ lᵉ)
--       ( 15ᵉ)
--   instance-telescope¹⁵ᵉ {Xᵉ = Xᵉ} =
--     cons-telescopeᵉ (λ xᵉ → instance-telescope¹⁴ᵉ {Xᵉ = Xᵉ xᵉ})

--   instance-telescope¹⁶ᵉ :
--     { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ l10ᵉ l11ᵉ l12ᵉ l13ᵉ l14ᵉ l15ᵉ l16ᵉ lᵉ : Level}
--     { A1ᵉ : UUᵉ l1ᵉ} {A2ᵉ : A1ᵉ → UUᵉ l2ᵉ} {A3ᵉ : (x1ᵉ : A1ᵉ) → A2ᵉ x1ᵉ → UUᵉ l3ᵉ}
--     { A4ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) → A3ᵉ x1ᵉ x2ᵉ → UUᵉ l4ᵉ}
--     { A5ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ) → UUᵉ l5ᵉ}
--     { A6ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) → UUᵉ l6ᵉ}
--     { A7ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ) → UUᵉ l7ᵉ}
--     { A8ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) → UUᵉ l8ᵉ}
--     { A9ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ) →
--       UUᵉ l9ᵉ}
--     { A10ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) →
--       UUᵉ l10ᵉ}
--     { A11ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ) →
--       UUᵉ l11ᵉ}
--     { A12ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ) → UUᵉ l12ᵉ}
--     { A13ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ) → UUᵉ l13ᵉ}
--     { A14ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ)
--       (x13ᵉ : A13ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ) → UUᵉ l14ᵉ}
--     { A15ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ)
--       (x13ᵉ : A13ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ)
--       (x14ᵉ : A14ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ) → UUᵉ l15ᵉ}
--     { A16ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ)
--       (x13ᵉ : A13ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ)
--       (x14ᵉ : A14ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ)
--       (x15ᵉ : A15ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ x14ᵉ) → UUᵉ l16ᵉ}
--     { Xᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ)
--       (x13ᵉ : A13ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ)
--       (x14ᵉ : A14ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ)
--       (x15ᵉ : A15ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ x14ᵉ)
--       (x16ᵉ : A16ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ x14ᵉ x15ᵉ) → UUᵉ lᵉ} →
--     telescopeᵉ
--       ( l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l7ᵉ ⊔ l8ᵉ ⊔ l9ᵉ ⊔ l10ᵉ ⊔ l11ᵉ ⊔ l12ᵉ ⊔ l13ᵉ ⊔
--         l14ᵉ ⊔ l15ᵉ ⊔ l16ᵉ ⊔ lᵉ)
--       ( 16ᵉ)
--   instance-telescope¹⁶ᵉ {Xᵉ = Xᵉ} =
--     cons-telescopeᵉ (λ xᵉ → instance-telescope¹⁵ᵉ {Xᵉ = Xᵉ xᵉ})

--   instance-telescope¹⁷ᵉ :
--     { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ l10ᵉ l11ᵉ l12ᵉ l13ᵉ l14ᵉ l15ᵉ l16ᵉ l17ᵉ lᵉ : Level}
--     { A1ᵉ : UUᵉ l1ᵉ} {A2ᵉ : A1ᵉ → UUᵉ l2ᵉ} {A3ᵉ : (x1ᵉ : A1ᵉ) → A2ᵉ x1ᵉ → UUᵉ l3ᵉ}
--     { A4ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) → A3ᵉ x1ᵉ x2ᵉ → UUᵉ l4ᵉ}
--     { A5ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ) → UUᵉ l5ᵉ}
--     { A6ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) → UUᵉ l6ᵉ}
--     { A7ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ) → UUᵉ l7ᵉ}
--     { A8ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) → UUᵉ l8ᵉ}
--     { A9ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ) →
--       UUᵉ l9ᵉ}
--     { A10ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) →
--       UUᵉ l10ᵉ}
--     { A11ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ) →
--       UUᵉ l11ᵉ}
--     { A12ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ) → UUᵉ l12ᵉ}
--     { A13ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ) → UUᵉ l13ᵉ}
--     { A14ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ)
--       (x13ᵉ : A13ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ) → UUᵉ l14ᵉ}
--     { A15ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ)
--       (x13ᵉ : A13ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ)
--       (x14ᵉ : A14ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ) → UUᵉ l15ᵉ}
--     { A16ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ)
--       (x13ᵉ : A13ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ)
--       (x14ᵉ : A14ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ)
--       (x15ᵉ : A15ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ x14ᵉ) → UUᵉ l16ᵉ}
--     { A17ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ)
--       (x13ᵉ : A13ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ)
--       (x14ᵉ : A14ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ)
--       (x15ᵉ : A15ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ x14ᵉ)
--       (x16ᵉ : A16ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ x14ᵉ x15ᵉ) → UUᵉ l17ᵉ}
--     { Xᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ)
--       (x13ᵉ : A13ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ)
--       (x14ᵉ : A14ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ)
--       (x15ᵉ : A15ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ x14ᵉ)
--       (x16ᵉ : A16ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ x14ᵉ x15ᵉ)
--       (x17ᵉ : A17ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ x14ᵉ x15ᵉ x16ᵉ) →
--       UUᵉ lᵉ} →
--     telescopeᵉ
--       ( l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l7ᵉ ⊔ l8ᵉ ⊔ l9ᵉ ⊔ l10ᵉ ⊔ l11ᵉ ⊔ l12ᵉ ⊔ l13ᵉ ⊔
--         l14ᵉ ⊔ l15ᵉ ⊔ l16ᵉ ⊔ l17ᵉ ⊔ lᵉ)
--       ( 17ᵉ)
--   instance-telescope¹⁷ᵉ {Xᵉ = Xᵉ} =
--     cons-telescopeᵉ (λ xᵉ → instance-telescope¹⁶ᵉ {Xᵉ = Xᵉ xᵉ})

--   instance-telescope¹⁸ᵉ :
--     { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ l10ᵉ l11ᵉ l12ᵉ l13ᵉ l14ᵉ l15ᵉ l16ᵉ l17ᵉ l18ᵉ lᵉ : Level}
--     { A1ᵉ : UUᵉ l1ᵉ} {A2ᵉ : A1ᵉ → UUᵉ l2ᵉ} {A3ᵉ : (x1ᵉ : A1ᵉ) → A2ᵉ x1ᵉ → UUᵉ l3ᵉ}
--     { A4ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) → A3ᵉ x1ᵉ x2ᵉ → UUᵉ l4ᵉ}
--     { A5ᵉ : (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ) → UUᵉ l5ᵉ}
--     { A6ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) → UUᵉ l6ᵉ}
--     { A7ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ) → UUᵉ l7ᵉ}
--     { A8ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) → UUᵉ l8ᵉ}
--     { A9ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ) →
--       UUᵉ l9ᵉ}
--     { A10ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) →
--       UUᵉ l10ᵉ}
--     { A11ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ) →
--       UUᵉ l11ᵉ}
--     { A12ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ) → UUᵉ l12ᵉ}
--     { A13ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ) → UUᵉ l13ᵉ}
--     { A14ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ)
--       (x13ᵉ : A13ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ) → UUᵉ l14ᵉ}
--     { A15ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ)
--       (x13ᵉ : A13ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ)
--       (x14ᵉ : A14ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ) → UUᵉ l15ᵉ}
--     { A16ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ)
--       (x13ᵉ : A13ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ)
--       (x14ᵉ : A14ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ)
--       (x15ᵉ : A15ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ x14ᵉ) → UUᵉ l16ᵉ}
--     { A17ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ)
--       (x13ᵉ : A13ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ)
--       (x14ᵉ : A14ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ)
--       (x15ᵉ : A15ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ x14ᵉ)
--       (x16ᵉ : A16ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ x14ᵉ x15ᵉ) → UUᵉ l17ᵉ}
--     { A18ᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ)
--       (x13ᵉ : A13ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ)
--       (x14ᵉ : A14ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ)
--       (x15ᵉ : A15ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ x14ᵉ)
--       (x16ᵉ : A16ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ x14ᵉ x15ᵉ)
--       (x17ᵉ : A17ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ x14ᵉ x15ᵉ x16ᵉ) →
--       UUᵉ l18ᵉ}
--     { Xᵉ :
--       (x1ᵉ : A1ᵉ) (x2ᵉ : A2ᵉ x1ᵉ) (x3ᵉ : A3ᵉ x1ᵉ x2ᵉ) (x4ᵉ : A4ᵉ x1ᵉ x2ᵉ x3ᵉ)
--       (x5ᵉ : A5ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ) (x6ᵉ : A6ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ)
--       (x7ᵉ : A7ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ) (x8ᵉ : A8ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ)
--       (x9ᵉ : A9ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ) (x10ᵉ : A10ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ)
--       (x11ᵉ : A11ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ)
--       (x12ᵉ : A12ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ)
--       (x13ᵉ : A13ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ)
--       (x14ᵉ : A14ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ)
--       (x15ᵉ : A15ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ x14ᵉ)
--       (x16ᵉ : A16ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ x14ᵉ x15ᵉ)
--       (x17ᵉ : A17ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ x14ᵉ x15ᵉ x16ᵉ)
--       (x18ᵉ : A18ᵉ x1ᵉ x2ᵉ x3ᵉ x4ᵉ x5ᵉ x6ᵉ x7ᵉ x8ᵉ x9ᵉ x10ᵉ x11ᵉ x12ᵉ x13ᵉ x14ᵉ x15ᵉ x16ᵉ x17ᵉ) →
--       UUᵉ lᵉ} →
--     telescopeᵉ
--       ( l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l7ᵉ ⊔ l8ᵉ ⊔ l9ᵉ ⊔ l10ᵉ ⊔ l11ᵉ ⊔ l12ᵉ ⊔ l13ᵉ ⊔
--         l14ᵉ ⊔ l15ᵉ ⊔ l16ᵉ ⊔ l17ᵉ ⊔ l18ᵉ ⊔ lᵉ)
--       ( 18ᵉ)
--   instance-telescope¹⁸ᵉ {Xᵉ = Xᵉ} =
--     cons-telescopeᵉ (λ xᵉ → instance-telescope¹⁷ᵉ {Xᵉ = Xᵉ xᵉ})
```

## See also

-ᵉ [Dependentᵉ telescopes](foundation.dependent-telescopes.mdᵉ)
-ᵉ [Iteratedᵉ Σ-types](foundation.iterated-dependent-pair-types.mdᵉ)
-ᵉ [Iteratedᵉ Π-types](foundation.iterated-dependent-product-types.mdᵉ)
