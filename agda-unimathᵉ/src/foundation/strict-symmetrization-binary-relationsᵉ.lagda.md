# Strict symmetrization of binary relations

```agda
module foundation.strict-symmetrization-binary-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.binary-relations-with-extensionsᵉ
open import foundation.binary-relations-with-liftsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.retractionsᵉ
```

</details>

## Idea

Givenᵉ aᵉ [binaryᵉ relation](foundation.binary-relations.mdᵉ) `R`ᵉ onᵉ `A`,ᵉ weᵉ canᵉ
constructᵉ aᵉ
{{#conceptᵉ "strictᵉ symmetrization"ᵉ Disambiguation="ofᵉ binaryᵉ relationsᵉ valuedᵉ in types"ᵉ Agda=strict-symmetrization-Relationᵉ}}
ofᵉ `R`.ᵉ Thisᵉ isᵉ aᵉ relationᵉ `Rˢ`ᵉ onᵉ `A`ᵉ thatᵉ isᵉ strictlyᵉ
[symmetric](foundation.symmetric-binary-relations.md).ᵉ I.e.,ᵉ forᵉ everyᵉ
`rᵉ : Rˢᵉ xᵉ y`,ᵉ weᵉ haveᵉ aᵉ symmetryᵉ operationᵉ `symᵉ rᵉ : Rˢᵉ yᵉ x`ᵉ suchᵉ thatᵉ

```text
  symᵉ (symᵉ rᵉ) ≐ᵉ r.ᵉ
```

Weᵉ defineᵉ theᵉ strictᵉ symmetrizationᵉ ofᵉ `R`ᵉ asᵉ

```text
  Rˢᵉ xᵉ yᵉ :=ᵉ Σᵉ (zᵉ : A),ᵉ (Rᵉ zᵉ xᵉ) ×ᵉ (Rᵉ zᵉ y).ᵉ
```

Ifᵉ theᵉ underlyingᵉ binaryᵉ relationᵉ isᵉ
[reflexive](foundation.reflexive-relations.md),ᵉ thenᵉ thisᵉ constructionᵉ hasᵉ aᵉ
unitᵉ mapᵉ `Rᵉ → Rˢ`.ᵉ Ifᵉ theᵉ binaryᵉ relationᵉ hasᵉ
[extensions](foundation.binary-relations-with-extensions.md),ᵉ thenᵉ itᵉ hasᵉ aᵉ
counitᵉ mapᵉ `Rˢᵉ → R`.ᵉ Noteᵉ thatᵉ weᵉ do notᵉ meanᵉ to implyᵉ thatᵉ theseᵉ mapsᵉ areᵉ
componentsᵉ ofᵉ anᵉ adjunction.ᵉ

Thereᵉ isᵉ alsoᵉ aᵉ dualᵉ notionᵉ ofᵉ strictᵉ symmetrizationᵉ ofᵉ binaryᵉ relationsᵉ definedᵉ
byᵉ

```text
  Rˢ-dualᵉ xᵉ yᵉ :=ᵉ Σᵉ (zᵉ : A),ᵉ (Rᵉ xᵉ zᵉ) ×ᵉ (Rᵉ yᵉ z).ᵉ
```

Theᵉ dualᵉ hasᵉ aᵉ counitᵉ mapᵉ ifᵉ theᵉ binaryᵉ relationᵉ hasᵉ
[lifts](foundation.binary-relations-with-lifts.mdᵉ) ratherᵉ thanᵉ extensions.ᵉ

Anᵉ essentialᵉ factᵉ aboutᵉ theᵉ strictᵉ symmetrizationᵉ ofᵉ aᵉ relationᵉ isᵉ thatᵉ theᵉ
strictᵉ symmetrizationᵉ ofᵉ anᵉ identityᵉ relationᵉ isᵉ equivalentᵉ to theᵉ identityᵉ
relation.ᵉ Weᵉ considerᵉ theᵉ strictᵉ symmetrizationᵉ ofᵉ theᵉ standardᵉ identityᵉ
relationᵉ in
[`foundation.strictly-involutive-identity-types`](foundation.strictly-involutive-identity-types.md).ᵉ

**Warning.**ᵉ Theᵉ strictᵉ symmetrizationᵉ isᵉ notᵉ theᵉ symmetricᵉ closure.ᵉ Forᵉ
instance,ᵉ ifᵉ theᵉ underlyingᵉ relationᵉ hasᵉ anᵉ initialᵉ element,ᵉ i.e.,ᵉ thereᵉ isᵉ anᵉ
elementᵉ `a`ᵉ suchᵉ thatᵉ `Rᵉ aᵉ x`ᵉ isᵉ
[contractible](foundation-core.contractible-types.mdᵉ) forᵉ everyᵉ `x`,ᵉ thenᵉ theᵉ
strictᵉ symmetrizationᵉ willᵉ beᵉ reflexive,ᵉ whileᵉ theᵉ symmetricᵉ closureᵉ needᵉ notᵉ
be.ᵉ

## Definitions

### Strict symmetrization of binary relations

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  where

  strict-symmetrization-Relationᵉ : Relationᵉ (l1ᵉ ⊔ l2ᵉ) Aᵉ
  strict-symmetrization-Relationᵉ xᵉ yᵉ = Σᵉ Aᵉ (λ zᵉ → Rᵉ zᵉ xᵉ ×ᵉ Rᵉ zᵉ yᵉ)

  symmetric-strict-symmetrization-Relationᵉ :
    is-symmetricᵉ strict-symmetrization-Relationᵉ
  symmetric-strict-symmetrization-Relationᵉ xᵉ yᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) = (zᵉ ,ᵉ qᵉ ,ᵉ pᵉ)

  is-involution-symmetric-strict-symmetrization-Relationᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : strict-symmetrization-Relationᵉ xᵉ yᵉ) →
    ( symmetric-strict-symmetrization-Relationᵉ yᵉ xᵉ
      ( symmetric-strict-symmetrization-Relationᵉ xᵉ yᵉ pᵉ)) ＝ᵉ
    ( pᵉ)
  is-involution-symmetric-strict-symmetrization-Relationᵉ pᵉ = reflᵉ

  unit-strict-symmetrization-Relationᵉ :
    is-reflexiveᵉ Rᵉ →
    {xᵉ yᵉ : Aᵉ} → Rᵉ xᵉ yᵉ → strict-symmetrization-Relationᵉ xᵉ yᵉ
  unit-strict-symmetrization-Relationᵉ rᵉ {xᵉ} pᵉ = (xᵉ ,ᵉ rᵉ xᵉ ,ᵉ pᵉ)

  counit-strict-symmetrization-Relationᵉ :
    has-extensions-Relationᵉ Rᵉ →
    {xᵉ yᵉ : Aᵉ} → strict-symmetrization-Relationᵉ xᵉ yᵉ → Rᵉ xᵉ yᵉ
  counit-strict-symmetrization-Relationᵉ Hᵉ (ᵉ_ ,ᵉ pᵉ ,ᵉ qᵉ) = Hᵉ pᵉ qᵉ
```

### Dual strict symmetrization of binary relations

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  where

  dual-strict-symmetrization-Relationᵉ : Relationᵉ (l1ᵉ ⊔ l2ᵉ) Aᵉ
  dual-strict-symmetrization-Relationᵉ xᵉ yᵉ = Σᵉ Aᵉ (λ zᵉ → Rᵉ xᵉ zᵉ ×ᵉ Rᵉ yᵉ zᵉ)

  symmetric-dual-strict-symmetrization-Relationᵉ :
    is-symmetricᵉ dual-strict-symmetrization-Relationᵉ
  symmetric-dual-strict-symmetrization-Relationᵉ xᵉ yᵉ (zᵉ ,ᵉ pᵉ ,ᵉ qᵉ) = (zᵉ ,ᵉ qᵉ ,ᵉ pᵉ)

  is-involution-symmetric-dual-strict-symmetrization-Relationᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : dual-strict-symmetrization-Relationᵉ xᵉ yᵉ) →
    ( symmetric-dual-strict-symmetrization-Relationᵉ yᵉ xᵉ
      ( symmetric-dual-strict-symmetrization-Relationᵉ xᵉ yᵉ pᵉ)) ＝ᵉ
    ( pᵉ)
  is-involution-symmetric-dual-strict-symmetrization-Relationᵉ pᵉ = reflᵉ

  unit-dual-strict-symmetrization-Relationᵉ :
    is-reflexiveᵉ Rᵉ →
    {xᵉ yᵉ : Aᵉ} → Rᵉ xᵉ yᵉ → dual-strict-symmetrization-Relationᵉ xᵉ yᵉ
  unit-dual-strict-symmetrization-Relationᵉ rᵉ {xᵉ} {yᵉ} pᵉ = (yᵉ ,ᵉ pᵉ ,ᵉ rᵉ yᵉ)

  counit-dual-strict-symmetrization-Relationᵉ :
    has-lifts-Relationᵉ Rᵉ →
    {xᵉ yᵉ : Aᵉ} → dual-strict-symmetrization-Relationᵉ xᵉ yᵉ → Rᵉ xᵉ yᵉ
  counit-dual-strict-symmetrization-Relationᵉ Hᵉ (ᵉ_ ,ᵉ pᵉ ,ᵉ qᵉ) = Hᵉ pᵉ qᵉ
```

## Properties

### The strict symmetrization of a reflexive relation is reflexive

Inᵉ fact,ᵉ `R`ᵉ doesᵉ notᵉ haveᵉ to beᵉ reflexiveᵉ forᵉ theᵉ strictᵉ symmetrizationᵉ to beᵉ
reflexive.ᵉ Itᵉ sufficesᵉ thatᵉ thereᵉ forᵉ everyᵉ elementᵉ ofᵉ `A`ᵉ isᵉ someᵉ otherᵉ elementᵉ
thatᵉ relatesᵉ to it.ᵉ Forᵉ instance,ᵉ theᵉ strictᵉ symmetrizationᵉ ofᵉ aᵉ relationᵉ with
anᵉ initialᵉ elementᵉ isᵉ alwaysᵉ reflexive.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  where

  refl-strict-symmetrization-Relation'ᵉ :
    ((xᵉ : Aᵉ) → Σᵉ Aᵉ (λ yᵉ → Rᵉ yᵉ xᵉ)) →
    is-reflexiveᵉ (strict-symmetrization-Relationᵉ Rᵉ)
  refl-strict-symmetrization-Relation'ᵉ rᵉ xᵉ = (pr1ᵉ (rᵉ xᵉ) ,ᵉ pr2ᵉ (rᵉ xᵉ) ,ᵉ pr2ᵉ (rᵉ xᵉ))

  refl-strict-symmetrization-Relationᵉ :
    is-reflexiveᵉ Rᵉ →
    is-reflexiveᵉ (strict-symmetrization-Relationᵉ Rᵉ)
  refl-strict-symmetrization-Relationᵉ rᵉ xᵉ = (xᵉ ,ᵉ rᵉ xᵉ ,ᵉ rᵉ xᵉ)
```

### The strict symmetrization of a relation with extensions satisfies all 2-horn filler conditions

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  (Hᵉ : has-extensions-Relationᵉ Rᵉ)
  where

  has-extensions-strict-symmetrization-Relationᵉ :
    has-extensions-Relationᵉ (strict-symmetrization-Relationᵉ Rᵉ)
  has-extensions-strict-symmetrization-Relationᵉ
    {xᵉ} (ᵉ_ ,ᵉ pᵉ ,ᵉ qᵉ) (ᵉ_ ,ᵉ p'ᵉ ,ᵉ q'ᵉ) = (xᵉ ,ᵉ Hᵉ pᵉ qᵉ ,ᵉ Hᵉ p'ᵉ q'ᵉ)

  has-lifts-strict-symmetrization-has-extensions-Relationᵉ :
    has-lifts-Relationᵉ (strict-symmetrization-Relationᵉ Rᵉ)
  has-lifts-strict-symmetrization-has-extensions-Relationᵉ
    {zᵉ = zᵉ} (wᵉ ,ᵉ pᵉ ,ᵉ qᵉ) (w'ᵉ ,ᵉ p'ᵉ ,ᵉ q'ᵉ) = (zᵉ ,ᵉ Hᵉ qᵉ pᵉ ,ᵉ Hᵉ q'ᵉ p'ᵉ)

  transitive-strict-symmetrization-has-extensions-Relationᵉ :
    is-transitiveᵉ (strict-symmetrization-Relationᵉ Rᵉ)
  transitive-strict-symmetrization-has-extensions-Relationᵉ
    xᵉ yᵉ zᵉ (wᵉ ,ᵉ pᵉ ,ᵉ qᵉ) (w'ᵉ ,ᵉ p'ᵉ ,ᵉ q'ᵉ) = (yᵉ ,ᵉ Hᵉ q'ᵉ p'ᵉ ,ᵉ Hᵉ pᵉ qᵉ)
```

### If the extension operation on the underlying relation is left unital, then the counit is a retraction of the unit of the strict symmetrization

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  (rᵉ : is-reflexiveᵉ Rᵉ) (Hᵉ : has-extensions-Relationᵉ Rᵉ)
  where

  is-retraction-counit-strict-symmetrization-Relationᵉ :
    {xᵉ yᵉ : Aᵉ} →
    ((pᵉ : Rᵉ xᵉ yᵉ) → Hᵉ (rᵉ xᵉ) pᵉ ＝ᵉ pᵉ) →
    is-retractionᵉ
      ( unit-strict-symmetrization-Relationᵉ Rᵉ rᵉ {xᵉ} {yᵉ})
      ( counit-strict-symmetrization-Relationᵉ Rᵉ Hᵉ {xᵉ} {yᵉ})
  is-retraction-counit-strict-symmetrization-Relationᵉ sᵉ = sᵉ
```