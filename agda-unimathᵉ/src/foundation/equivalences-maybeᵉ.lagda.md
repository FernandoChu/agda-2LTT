# Equivalences on `Maybe`

```agda
module foundation.equivalences-maybeᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-coproduct-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.maybeᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-maybeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.coproduct-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
```

</details>

## Idea

Forᵉ anyᵉ twoᵉ typesᵉ `X`ᵉ andᵉ `Y`,ᵉ weᵉ haveᵉ `(Xᵉ ≃ᵉ Yᵉ) ↔ᵉ (Maybeᵉ Xᵉ ≃ᵉ Maybeᵉ Y)`.ᵉ

## Definition

### The action of the Maybe modality on equivalences

```agda
equiv-Maybeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Xᵉ ≃ᵉ Yᵉ) → Maybeᵉ Xᵉ ≃ᵉ Maybeᵉ Yᵉ
equiv-Maybeᵉ eᵉ = equiv-coproductᵉ eᵉ id-equivᵉ
```

### Equivalences of Maybe-structures on a type

```agda
equiv-maybe-structureᵉ :
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Yᵉ Zᵉ : maybe-structureᵉ Xᵉ) → UUᵉ l1ᵉ
equiv-maybe-structureᵉ Yᵉ Zᵉ =
  Σᵉ (pr1ᵉ Yᵉ ≃ᵉ pr1ᵉ Zᵉ) (λ eᵉ → htpy-equivᵉ (pr2ᵉ Yᵉ) (pr2ᵉ Zᵉ ∘eᵉ equiv-Maybeᵉ eᵉ))

id-equiv-maybe-structureᵉ :
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Yᵉ : maybe-structureᵉ Xᵉ) → equiv-maybe-structureᵉ Yᵉ Yᵉ
id-equiv-maybe-structureᵉ Yᵉ =
  pairᵉ id-equivᵉ (ind-Maybeᵉ (pairᵉ refl-htpyᵉ reflᵉ))

equiv-eq-maybe-structureᵉ :
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Yᵉ Zᵉ : maybe-structureᵉ Xᵉ) →
  Yᵉ ＝ᵉ Zᵉ → equiv-maybe-structureᵉ Yᵉ Zᵉ
equiv-eq-maybe-structureᵉ Yᵉ .Yᵉ reflᵉ = id-equiv-maybe-structureᵉ Yᵉ
```

## Properties

### If `f : Maybe X → Maybe Y` is an injective map and `f (inl x)` is an exception, then `f exception` is not an exception

```agda
abstract
  is-not-exception-injective-map-exception-Maybeᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {fᵉ : Maybeᵉ Xᵉ → Maybeᵉ Yᵉ} →
    is-injectiveᵉ fᵉ → (xᵉ : Xᵉ) → is-exception-Maybeᵉ (fᵉ (inlᵉ xᵉ)) →
    is-not-exception-Maybeᵉ (fᵉ exception-Maybeᵉ)
  is-not-exception-injective-map-exception-Maybeᵉ is-inj-fᵉ xᵉ pᵉ qᵉ =
    is-not-exception-unit-Maybeᵉ xᵉ (is-inj-fᵉ (pᵉ ∙ᵉ invᵉ qᵉ))

abstract
  is-not-exception-map-equiv-exception-Maybeᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Maybeᵉ Xᵉ ≃ᵉ Maybeᵉ Yᵉ) (xᵉ : Xᵉ) →
    is-exception-Maybeᵉ (map-equivᵉ eᵉ (inlᵉ xᵉ)) →
    is-not-exception-Maybeᵉ (map-equivᵉ eᵉ exception-Maybeᵉ)
  is-not-exception-map-equiv-exception-Maybeᵉ eᵉ =
    is-not-exception-injective-map-exception-Maybeᵉ (is-injective-equivᵉ eᵉ)

abstract
  is-not-exception-emb-exception-Maybeᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Maybeᵉ Xᵉ ↪ᵉ Maybeᵉ Yᵉ)
    (xᵉ : Xᵉ) → is-exception-Maybeᵉ (map-embᵉ eᵉ (inlᵉ xᵉ)) →
    is-not-exception-Maybeᵉ (map-embᵉ eᵉ exception-Maybeᵉ)
  is-not-exception-emb-exception-Maybeᵉ eᵉ =
    is-not-exception-injective-map-exception-Maybeᵉ (is-injective-embᵉ eᵉ)
```

### If `f` is injective and `f (inl x)` is an exception, then `f exception` is a value

```agda
is-value-injective-map-exception-Maybeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {fᵉ : Maybeᵉ Xᵉ → Maybeᵉ Yᵉ} →
  is-injectiveᵉ fᵉ → (xᵉ : Xᵉ) → is-exception-Maybeᵉ (fᵉ (inlᵉ xᵉ)) →
  is-value-Maybeᵉ (fᵉ exception-Maybeᵉ)
is-value-injective-map-exception-Maybeᵉ {fᵉ = fᵉ} is-inj-fᵉ xᵉ Hᵉ =
  is-value-is-not-exception-Maybeᵉ
    ( fᵉ exception-Maybeᵉ)
    ( is-not-exception-injective-map-exception-Maybeᵉ is-inj-fᵉ xᵉ Hᵉ)

value-injective-map-exception-Maybeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {fᵉ : Maybeᵉ Xᵉ → Maybeᵉ Yᵉ} →
  is-injectiveᵉ fᵉ → (xᵉ : Xᵉ) → is-exception-Maybeᵉ (fᵉ (inlᵉ xᵉ)) → Yᵉ
value-injective-map-exception-Maybeᵉ {fᵉ = fᵉ} is-inj-fᵉ xᵉ Hᵉ =
  value-is-value-Maybeᵉ
    ( fᵉ exception-Maybeᵉ)
    ( is-value-injective-map-exception-Maybeᵉ is-inj-fᵉ xᵉ Hᵉ)

comp-injective-map-exception-Maybeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {fᵉ : Maybeᵉ Xᵉ → Maybeᵉ Yᵉ} →
  (is-inj-fᵉ : is-injectiveᵉ fᵉ) (xᵉ : Xᵉ) (Hᵉ : is-exception-Maybeᵉ (fᵉ (inlᵉ xᵉ))) →
  inlᵉ (value-injective-map-exception-Maybeᵉ is-inj-fᵉ xᵉ Hᵉ) ＝ᵉ
  fᵉ exception-Maybeᵉ
comp-injective-map-exception-Maybeᵉ {fᵉ = fᵉ} is-inj-fᵉ xᵉ Hᵉ =
  eq-is-value-Maybeᵉ
    ( fᵉ exception-Maybeᵉ)
    ( is-value-injective-map-exception-Maybeᵉ is-inj-fᵉ xᵉ Hᵉ)
```

### For any equivalence `e : Maybe X ≃ Maybe Y`, if `e (inl x)` is an exception, then `e exception` is a value

```agda
is-value-map-equiv-exception-Maybeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Maybeᵉ Xᵉ ≃ᵉ Maybeᵉ Yᵉ) (xᵉ : Xᵉ) →
  is-exception-Maybeᵉ (map-equivᵉ eᵉ (inlᵉ xᵉ)) →
  is-value-Maybeᵉ (map-equivᵉ eᵉ exception-Maybeᵉ)
is-value-map-equiv-exception-Maybeᵉ eᵉ xᵉ Hᵉ =
  is-value-is-not-exception-Maybeᵉ
    ( map-equivᵉ eᵉ exception-Maybeᵉ)
    ( is-not-exception-map-equiv-exception-Maybeᵉ eᵉ xᵉ Hᵉ)

value-map-equiv-exception-Maybeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Maybeᵉ Xᵉ ≃ᵉ Maybeᵉ Yᵉ) (xᵉ : Xᵉ) →
  is-exception-Maybeᵉ (map-equivᵉ eᵉ (inlᵉ xᵉ)) → Yᵉ
value-map-equiv-exception-Maybeᵉ eᵉ xᵉ Hᵉ =
  value-is-value-Maybeᵉ
    ( map-equivᵉ eᵉ exception-Maybeᵉ)
    ( is-value-map-equiv-exception-Maybeᵉ eᵉ xᵉ Hᵉ)

compute-map-equiv-exception-Maybeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Maybeᵉ Xᵉ ≃ᵉ Maybeᵉ Yᵉ) (xᵉ : Xᵉ) →
  (Hᵉ : is-exception-Maybeᵉ (map-equivᵉ eᵉ (inlᵉ xᵉ))) →
  inlᵉ (value-map-equiv-exception-Maybeᵉ eᵉ xᵉ Hᵉ) ＝ᵉ map-equivᵉ eᵉ exception-Maybeᵉ
compute-map-equiv-exception-Maybeᵉ eᵉ xᵉ Hᵉ =
  eq-is-value-Maybeᵉ
    ( map-equivᵉ eᵉ exception-Maybeᵉ)
    ( is-value-map-equiv-exception-Maybeᵉ eᵉ xᵉ Hᵉ)
```

### Injective maps `Maybe X → Maybe Y` can be restricted to maps `X → Y`

```agda
restrict-injective-map-Maybe'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {fᵉ : Maybeᵉ Xᵉ → Maybeᵉ Yᵉ} →
  is-injectiveᵉ fᵉ → (xᵉ : Xᵉ) (uᵉ : Maybeᵉ Yᵉ) (pᵉ : fᵉ (inlᵉ xᵉ) ＝ᵉ uᵉ) → Yᵉ
restrict-injective-map-Maybe'ᵉ {fᵉ = fᵉ} is-inj-fᵉ xᵉ (inlᵉ yᵉ) pᵉ = yᵉ
restrict-injective-map-Maybe'ᵉ {fᵉ = fᵉ} is-inj-fᵉ xᵉ (inrᵉ starᵉ) pᵉ =
  value-injective-map-exception-Maybeᵉ is-inj-fᵉ xᵉ pᵉ

restrict-injective-map-Maybeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {fᵉ : Maybeᵉ Xᵉ → Maybeᵉ Yᵉ} →
  is-injectiveᵉ fᵉ → Xᵉ → Yᵉ
restrict-injective-map-Maybeᵉ {fᵉ = fᵉ} is-inj-fᵉ xᵉ =
  restrict-injective-map-Maybe'ᵉ is-inj-fᵉ xᵉ (fᵉ (inlᵉ xᵉ)) reflᵉ

compute-restrict-injective-map-is-exception-Maybe'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {fᵉ : Maybeᵉ Xᵉ → Maybeᵉ Yᵉ} →
  (is-inj-fᵉ : is-injectiveᵉ fᵉ) (xᵉ : Xᵉ) (uᵉ : Maybeᵉ Yᵉ) (pᵉ : fᵉ (inlᵉ xᵉ) ＝ᵉ uᵉ) →
  is-exception-Maybeᵉ (fᵉ (inlᵉ xᵉ)) →
  inlᵉ (restrict-injective-map-Maybe'ᵉ is-inj-fᵉ xᵉ uᵉ pᵉ) ＝ᵉ fᵉ exception-Maybeᵉ
compute-restrict-injective-map-is-exception-Maybe'ᵉ
  {fᵉ = fᵉ} is-inj-fᵉ xᵉ (inlᵉ yᵉ) pᵉ qᵉ =
  ex-falsoᵉ (is-not-exception-unit-Maybeᵉ yᵉ (invᵉ pᵉ ∙ᵉ qᵉ))
compute-restrict-injective-map-is-exception-Maybe'ᵉ
  {fᵉ = fᵉ} is-inj-fᵉ xᵉ (inrᵉ starᵉ) pᵉ qᵉ =
  comp-injective-map-exception-Maybeᵉ is-inj-fᵉ xᵉ pᵉ

compute-restrict-injective-map-is-exception-Maybeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {fᵉ : Maybeᵉ Xᵉ → Maybeᵉ Yᵉ} →
  (is-inj-fᵉ : is-injectiveᵉ fᵉ) (xᵉ : Xᵉ) → is-exception-Maybeᵉ (fᵉ (inlᵉ xᵉ)) →
  inlᵉ (restrict-injective-map-Maybeᵉ is-inj-fᵉ xᵉ) ＝ᵉ fᵉ exception-Maybeᵉ
compute-restrict-injective-map-is-exception-Maybeᵉ {fᵉ = fᵉ} is-inj-fᵉ xᵉ =
  compute-restrict-injective-map-is-exception-Maybe'ᵉ is-inj-fᵉ xᵉ (fᵉ (inlᵉ xᵉ)) reflᵉ

compute-restrict-injective-map-is-not-exception-Maybe'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {fᵉ : Maybeᵉ Xᵉ → Maybeᵉ Yᵉ} →
  (is-inj-fᵉ : is-injectiveᵉ fᵉ) (xᵉ : Xᵉ) (uᵉ : Maybeᵉ Yᵉ) (pᵉ : fᵉ (inlᵉ xᵉ) ＝ᵉ uᵉ) →
  is-not-exception-Maybeᵉ (fᵉ (inlᵉ xᵉ)) →
  inlᵉ (restrict-injective-map-Maybe'ᵉ is-inj-fᵉ xᵉ uᵉ pᵉ) ＝ᵉ fᵉ (inlᵉ xᵉ)
compute-restrict-injective-map-is-not-exception-Maybe'ᵉ
  is-inj-fᵉ xᵉ (inlᵉ yᵉ) pᵉ Hᵉ =
  invᵉ pᵉ
compute-restrict-injective-map-is-not-exception-Maybe'ᵉ
  is-inj-fᵉ xᵉ (inrᵉ starᵉ) pᵉ Hᵉ =
  ex-falsoᵉ (Hᵉ pᵉ)

compute-restrict-injective-map-is-not-exception-Maybeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {fᵉ : Maybeᵉ Xᵉ → Maybeᵉ Yᵉ} →
  (is-inj-fᵉ : is-injectiveᵉ fᵉ) (xᵉ : Xᵉ) → is-not-exception-Maybeᵉ (fᵉ (inlᵉ xᵉ)) →
  inlᵉ (restrict-injective-map-Maybeᵉ is-inj-fᵉ xᵉ) ＝ᵉ fᵉ (inlᵉ xᵉ)
compute-restrict-injective-map-is-not-exception-Maybeᵉ {fᵉ = fᵉ} is-inj-fᵉ xᵉ =
  compute-restrict-injective-map-is-not-exception-Maybe'ᵉ is-inj-fᵉ xᵉ (fᵉ (inlᵉ xᵉ))
    reflᵉ
```

### Any equivalence `Maybe X ≃ Maybe Y` induces a map `X → Y`

Weᵉ don'tᵉ useᵉ with-abstractionᵉ to keepᵉ fullᵉ controlᵉ overᵉ theᵉ definitionalᵉ
equalities,ᵉ soᵉ weᵉ giveᵉ theᵉ definitionᵉ in twoᵉ steps.ᵉ Afterᵉ theᵉ definitionᵉ isᵉ
complete,ᵉ weᵉ alsoᵉ proveᵉ twoᵉ computationᵉ rules.ᵉ Sinceᵉ weᵉ willᵉ proveᵉ computationᵉ
rules,ᵉ weᵉ makeᵉ theᵉ definitionᵉ abstract.ᵉ

```agda
map-equiv-equiv-Maybe'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Maybeᵉ Xᵉ ≃ᵉ Maybeᵉ Yᵉ)
  (xᵉ : Xᵉ) (uᵉ : Maybeᵉ Yᵉ) (pᵉ : map-equivᵉ eᵉ (inlᵉ xᵉ) ＝ᵉ uᵉ) → Yᵉ
map-equiv-equiv-Maybe'ᵉ eᵉ =
  restrict-injective-map-Maybe'ᵉ (is-injective-equivᵉ eᵉ)

map-equiv-equiv-Maybeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Maybeᵉ Xᵉ ≃ᵉ Maybeᵉ Yᵉ) → Xᵉ → Yᵉ
map-equiv-equiv-Maybeᵉ eᵉ =
  restrict-injective-map-Maybeᵉ (is-injective-equivᵉ eᵉ)

compute-map-equiv-equiv-is-exception-Maybe'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Maybeᵉ Xᵉ ≃ᵉ Maybeᵉ Yᵉ) (xᵉ : Xᵉ) →
  (uᵉ : Maybeᵉ Yᵉ) (pᵉ : map-equivᵉ eᵉ (inlᵉ xᵉ) ＝ᵉ uᵉ) →
  is-exception-Maybeᵉ (map-equivᵉ eᵉ (inlᵉ xᵉ)) →
  inlᵉ (map-equiv-equiv-Maybe'ᵉ eᵉ xᵉ uᵉ pᵉ) ＝ᵉ map-equivᵉ eᵉ exception-Maybeᵉ
compute-map-equiv-equiv-is-exception-Maybe'ᵉ eᵉ =
  compute-restrict-injective-map-is-exception-Maybe'ᵉ (is-injective-equivᵉ eᵉ)

compute-map-equiv-equiv-is-exception-Maybeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Maybeᵉ Xᵉ ≃ᵉ Maybeᵉ Yᵉ) (xᵉ : Xᵉ) →
  is-exception-Maybeᵉ (map-equivᵉ eᵉ (inlᵉ xᵉ)) →
  inlᵉ (map-equiv-equiv-Maybeᵉ eᵉ xᵉ) ＝ᵉ map-equivᵉ eᵉ exception-Maybeᵉ
compute-map-equiv-equiv-is-exception-Maybeᵉ eᵉ xᵉ =
  compute-map-equiv-equiv-is-exception-Maybe'ᵉ eᵉ xᵉ (map-equivᵉ eᵉ (inlᵉ xᵉ)) reflᵉ

compute-map-equiv-equiv-is-not-exception-Maybe'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Maybeᵉ Xᵉ ≃ᵉ Maybeᵉ Yᵉ) (xᵉ : Xᵉ) →
  (uᵉ : Maybeᵉ Yᵉ) (pᵉ : map-equivᵉ eᵉ (inlᵉ xᵉ) ＝ᵉ uᵉ) →
  is-not-exception-Maybeᵉ (map-equivᵉ eᵉ (inlᵉ xᵉ)) →
  inlᵉ (map-equiv-equiv-Maybe'ᵉ eᵉ xᵉ uᵉ pᵉ) ＝ᵉ map-equivᵉ eᵉ (inlᵉ xᵉ)
compute-map-equiv-equiv-is-not-exception-Maybe'ᵉ eᵉ xᵉ (inlᵉ yᵉ) pᵉ Hᵉ =
  invᵉ pᵉ
compute-map-equiv-equiv-is-not-exception-Maybe'ᵉ eᵉ xᵉ (inrᵉ starᵉ) pᵉ Hᵉ =
  ex-falsoᵉ (Hᵉ pᵉ)

compute-map-equiv-equiv-is-not-exception-Maybeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Maybeᵉ Xᵉ ≃ᵉ Maybeᵉ Yᵉ) (xᵉ : Xᵉ) →
  is-not-exception-Maybeᵉ (map-equivᵉ eᵉ (inlᵉ xᵉ)) →
  inlᵉ (map-equiv-equiv-Maybeᵉ eᵉ xᵉ) ＝ᵉ map-equivᵉ eᵉ (inlᵉ xᵉ)
compute-map-equiv-equiv-is-not-exception-Maybeᵉ eᵉ xᵉ =
  compute-map-equiv-equiv-is-not-exception-Maybe'ᵉ eᵉ xᵉ (map-equivᵉ eᵉ (inlᵉ xᵉ)) reflᵉ
```

### Any equivalence `Maybe X ≃ Maybe Y` induces a map `Y → X`

```agda
map-inv-equiv-equiv-Maybeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Maybeᵉ Xᵉ ≃ᵉ Maybeᵉ Yᵉ) → Yᵉ → Xᵉ
map-inv-equiv-equiv-Maybeᵉ eᵉ =
  map-equiv-equiv-Maybeᵉ (inv-equivᵉ eᵉ)

compute-map-inv-equiv-equiv-is-exception-Maybeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Maybeᵉ Xᵉ ≃ᵉ Maybeᵉ Yᵉ) (yᵉ : Yᵉ) →
  is-exception-Maybeᵉ (map-inv-equivᵉ eᵉ (inlᵉ yᵉ)) →
  inlᵉ (map-inv-equiv-equiv-Maybeᵉ eᵉ yᵉ) ＝ᵉ map-inv-equivᵉ eᵉ exception-Maybeᵉ
compute-map-inv-equiv-equiv-is-exception-Maybeᵉ eᵉ =
  compute-map-equiv-equiv-is-exception-Maybeᵉ (inv-equivᵉ eᵉ)

compute-map-inv-equiv-equiv-is-not-exception-Maybeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Maybeᵉ Xᵉ ≃ᵉ Maybeᵉ Yᵉ) (yᵉ : Yᵉ) →
  ( fᵉ : is-not-exception-Maybeᵉ (map-inv-equivᵉ eᵉ (inlᵉ yᵉ))) →
  inlᵉ (map-inv-equiv-equiv-Maybeᵉ eᵉ yᵉ) ＝ᵉ map-inv-equivᵉ eᵉ (inlᵉ yᵉ)
compute-map-inv-equiv-equiv-is-not-exception-Maybeᵉ eᵉ =
  compute-map-equiv-equiv-is-not-exception-Maybeᵉ (inv-equivᵉ eᵉ)
```

### The map `map-inv-equiv-equiv-Maybe e` is a section of `map-equiv-equiv-Maybe e`

```agda
abstract
  is-section-map-inv-equiv-equiv-Maybeᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Maybeᵉ Xᵉ ≃ᵉ Maybeᵉ Yᵉ) →
    (map-equiv-equiv-Maybeᵉ eᵉ ∘ᵉ map-inv-equiv-equiv-Maybeᵉ eᵉ) ~ᵉ idᵉ
  is-section-map-inv-equiv-equiv-Maybeᵉ eᵉ yᵉ with
    is-decidable-is-exception-Maybeᵉ (map-inv-equivᵉ eᵉ (inlᵉ yᵉ))
  ... | inlᵉ pᵉ =
    is-injective-unit-Maybeᵉ
      ( ( compute-map-equiv-equiv-is-exception-Maybeᵉ eᵉ
          ( map-inv-equiv-equiv-Maybeᵉ eᵉ yᵉ)
          ( ( apᵉ
              ( map-equivᵉ eᵉ)
              ( compute-map-inv-equiv-equiv-is-exception-Maybeᵉ eᵉ yᵉ pᵉ)) ∙ᵉ
            ( is-section-map-inv-equivᵉ eᵉ exception-Maybeᵉ))) ∙ᵉ
        ( ( apᵉ (map-equivᵉ eᵉ) (invᵉ pᵉ)) ∙ᵉ
          ( is-section-map-inv-equivᵉ eᵉ (inlᵉ yᵉ))))
  ... | inrᵉ fᵉ =
    is-injective-unit-Maybeᵉ
      ( ( compute-map-equiv-equiv-is-not-exception-Maybeᵉ eᵉ
          ( map-inv-equiv-equiv-Maybeᵉ eᵉ yᵉ)
          ( is-not-exception-is-value-Maybeᵉ
            ( map-equivᵉ eᵉ (inlᵉ (map-inv-equiv-equiv-Maybeᵉ eᵉ yᵉ)))
            ( pairᵉ yᵉ
              ( invᵉ
                ( ( apᵉ
                    ( map-equivᵉ eᵉ)
                    ( compute-map-inv-equiv-equiv-is-not-exception-Maybeᵉ
                        eᵉ yᵉ fᵉ)) ∙ᵉ
                  ( is-section-map-inv-equivᵉ eᵉ (inlᵉ yᵉ))))))) ∙ᵉ
        ( ( apᵉ
            ( map-equivᵉ eᵉ)
            ( compute-map-inv-equiv-equiv-is-not-exception-Maybeᵉ eᵉ yᵉ fᵉ)) ∙ᵉ
          ( is-section-map-inv-equivᵉ eᵉ (inlᵉ yᵉ))))
```

### The map `map-inv-equiv-equiv-Maybe e` is a retraction of the map `map-equiv-equiv-Maybe e`

```agda
abstract
  is-retraction-map-inv-equiv-equiv-Maybeᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Maybeᵉ Xᵉ ≃ᵉ Maybeᵉ Yᵉ) →
    (map-inv-equiv-equiv-Maybeᵉ eᵉ ∘ᵉ map-equiv-equiv-Maybeᵉ eᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-equiv-equiv-Maybeᵉ eᵉ xᵉ with
    is-decidable-is-exception-Maybeᵉ (map-equivᵉ eᵉ (inlᵉ xᵉ))
  ... | inlᵉ pᵉ =
    is-injective-unit-Maybeᵉ
      ( ( compute-map-inv-equiv-equiv-is-exception-Maybeᵉ eᵉ
          ( map-equiv-equiv-Maybeᵉ eᵉ xᵉ)
          ( ( apᵉ
              ( map-inv-equivᵉ eᵉ)
              ( compute-map-equiv-equiv-is-exception-Maybeᵉ eᵉ xᵉ pᵉ)) ∙ᵉ
            ( is-retraction-map-inv-equivᵉ eᵉ exception-Maybeᵉ))) ∙ᵉ
        ( ( apᵉ (map-inv-equivᵉ eᵉ) (invᵉ pᵉ)) ∙ᵉ
          ( is-retraction-map-inv-equivᵉ eᵉ (inlᵉ xᵉ))))
  ... | inrᵉ fᵉ =
    is-injective-unit-Maybeᵉ
      ( ( compute-map-inv-equiv-equiv-is-not-exception-Maybeᵉ eᵉ
          ( map-equiv-equiv-Maybeᵉ eᵉ xᵉ)
          ( is-not-exception-is-value-Maybeᵉ
            ( map-inv-equivᵉ eᵉ (inlᵉ (map-equiv-equiv-Maybeᵉ eᵉ xᵉ)))
            ( pairᵉ xᵉ
              ( invᵉ
                ( ( apᵉ
                    ( map-inv-equivᵉ eᵉ)
                    ( compute-map-equiv-equiv-is-not-exception-Maybeᵉ
                        eᵉ xᵉ fᵉ)) ∙ᵉ
                  ( is-retraction-map-inv-equivᵉ eᵉ (inlᵉ xᵉ))))))) ∙ᵉ
        ( ( apᵉ
            ( map-inv-equivᵉ eᵉ)
            ( compute-map-equiv-equiv-is-not-exception-Maybeᵉ eᵉ xᵉ fᵉ)) ∙ᵉ
          ( is-retraction-map-inv-equivᵉ eᵉ (inlᵉ xᵉ))))
```

### The function `map-equiv-equiv-Maybe` is an equivalence

```agda
abstract
  is-equiv-map-equiv-equiv-Maybeᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Maybeᵉ Xᵉ ≃ᵉ Maybeᵉ Yᵉ) →
    is-equivᵉ (map-equiv-equiv-Maybeᵉ eᵉ)
  is-equiv-map-equiv-equiv-Maybeᵉ eᵉ =
    is-equiv-is-invertibleᵉ
      ( map-inv-equiv-equiv-Maybeᵉ eᵉ)
      ( is-section-map-inv-equiv-equiv-Maybeᵉ eᵉ)
      ( is-retraction-map-inv-equiv-equiv-Maybeᵉ eᵉ)

equiv-equiv-Maybeᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} → (Maybeᵉ Xᵉ ≃ᵉ Maybeᵉ Yᵉ) → (Xᵉ ≃ᵉ Yᵉ)
pr1ᵉ (equiv-equiv-Maybeᵉ eᵉ) = map-equiv-equiv-Maybeᵉ eᵉ
pr2ᵉ (equiv-equiv-Maybeᵉ eᵉ) = is-equiv-map-equiv-equiv-Maybeᵉ eᵉ

compute-equiv-equiv-Maybe-id-equivᵉ :
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} →
  equiv-equiv-Maybeᵉ id-equivᵉ ＝ᵉ id-equivᵉ {Aᵉ = Xᵉ}
compute-equiv-equiv-Maybe-id-equivᵉ = eq-htpy-equivᵉ refl-htpyᵉ
```

### For any set `X`, the type of automorphisms on `X` is equivalent to the type of automorphisms on `Maybe X` that fix the exception

```agda
module _
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ)
  where

  extend-equiv-Maybeᵉ :
    (type-Setᵉ Xᵉ ≃ᵉ type-Setᵉ Xᵉ) ≃ᵉ
    ( Σᵉ ( Maybeᵉ (type-Setᵉ Xᵉ) ≃ᵉ Maybeᵉ (type-Setᵉ Xᵉ))
        ( λ eᵉ → map-equivᵉ eᵉ (inrᵉ starᵉ) ＝ᵉ inrᵉ starᵉ))
  pr1ᵉ (pr1ᵉ extend-equiv-Maybeᵉ fᵉ) = equiv-coproductᵉ fᵉ id-equivᵉ
  pr2ᵉ (pr1ᵉ extend-equiv-Maybeᵉ fᵉ) = reflᵉ
  pr2ᵉ extend-equiv-Maybeᵉ =
    is-equiv-is-invertibleᵉ
      ( λ fᵉ → pr1ᵉ (retraction-equiv-coproductᵉ (pr1ᵉ fᵉ) id-equivᵉ (pᵉ fᵉ)))
      ( λ fᵉ →
        ( eq-pair-Σᵉ
          ( invᵉ
            ( eq-htpy-equivᵉ
              ( pr2ᵉ (retraction-equiv-coproductᵉ (pr1ᵉ fᵉ) id-equivᵉ (pᵉ fᵉ)))))
          ( eq-is-propᵉ
            ( pr2ᵉ
              ( Id-Propᵉ
                ( pairᵉ
                  ( Maybeᵉ (type-Setᵉ Xᵉ))
                  ( is-set-coproductᵉ (is-set-type-Setᵉ Xᵉ) is-set-unitᵉ))
                ( map-equivᵉ (pr1ᵉ fᵉ) (inrᵉ starᵉ))
                ( inrᵉ starᵉ))))))
      ( λ fᵉ → eq-equiv-eq-map-equivᵉ reflᵉ)
    where
    pᵉ :
      ( fᵉ :
        ( Σᵉ ( Maybeᵉ (type-Setᵉ Xᵉ) ≃ᵉ Maybeᵉ (type-Setᵉ Xᵉ))
            ( λ eᵉ → map-equivᵉ eᵉ (inrᵉ starᵉ) ＝ᵉ inrᵉ starᵉ)))
      ( bᵉ : unitᵉ) →
      map-equivᵉ (pr1ᵉ fᵉ) (inrᵉ bᵉ) ＝ᵉ inrᵉ bᵉ
    pᵉ fᵉ starᵉ = pr2ᵉ fᵉ

  computation-extend-equiv-Maybeᵉ :
    (fᵉ : type-Setᵉ Xᵉ ≃ᵉ type-Setᵉ Xᵉ) (xᵉ yᵉ : type-Setᵉ Xᵉ) → map-equivᵉ fᵉ xᵉ ＝ᵉ yᵉ →
    map-equivᵉ (pr1ᵉ (map-equivᵉ extend-equiv-Maybeᵉ fᵉ)) (inlᵉ xᵉ) ＝ᵉ inlᵉ yᵉ
  computation-extend-equiv-Maybeᵉ fᵉ xᵉ yᵉ pᵉ = apᵉ inlᵉ pᵉ

  computation-inv-extend-equiv-Maybeᵉ :
    (fᵉ : Maybeᵉ (type-Setᵉ Xᵉ) ≃ᵉ Maybeᵉ (type-Setᵉ Xᵉ))
    (pᵉ : map-equivᵉ fᵉ (inrᵉ starᵉ) ＝ᵉ inrᵉ starᵉ) (xᵉ : type-Setᵉ Xᵉ) →
    inlᵉ (map-equivᵉ (map-inv-equivᵉ extend-equiv-Maybeᵉ (pairᵉ fᵉ pᵉ)) xᵉ) ＝ᵉ
    map-equivᵉ fᵉ (inlᵉ xᵉ)
  computation-inv-extend-equiv-Maybeᵉ fᵉ pᵉ xᵉ =
    htpy-eq-equivᵉ
      ( pr1ᵉ (pair-eq-Σᵉ (pr2ᵉ (pr1ᵉ (pr2ᵉ extend-equiv-Maybeᵉ)) (pairᵉ fᵉ pᵉ))))
      ( inlᵉ xᵉ)

  comp-extend-equiv-Maybeᵉ :
    (fᵉ gᵉ : type-Setᵉ Xᵉ ≃ᵉ type-Setᵉ Xᵉ) →
    htpy-equivᵉ
      ( pr1ᵉ (map-equivᵉ extend-equiv-Maybeᵉ (fᵉ ∘eᵉ gᵉ)))
      ( ( pr1ᵉ (map-equivᵉ extend-equiv-Maybeᵉ fᵉ)) ∘eᵉ
        ( pr1ᵉ (map-equivᵉ extend-equiv-Maybeᵉ gᵉ)))
  comp-extend-equiv-Maybeᵉ fᵉ gᵉ =
    preserves-comp-map-coproductᵉ (map-equivᵉ gᵉ) (map-equivᵉ fᵉ) idᵉ idᵉ
```