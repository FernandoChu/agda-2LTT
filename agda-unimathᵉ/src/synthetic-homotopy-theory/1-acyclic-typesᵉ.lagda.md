# `1`-acyclic types

```agda
module synthetic-homotopy-theory.1-acyclic-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.binary-transportᵉ
open import foundation.constant-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.diagonal-maps-of-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.propositionsᵉ
open import foundation.set-truncationsᵉ
open import foundation.setsᵉ
open import foundation.truncated-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.0-acyclic-typesᵉ
open import synthetic-homotopy-theory.loop-spacesᵉ
open import synthetic-homotopy-theory.truncated-acyclic-mapsᵉ
open import synthetic-homotopy-theory.truncated-acyclic-typesᵉ
```

</details>

## Idea

Aᵉ typeᵉ isᵉ **`1`-acyclic**ᵉ ifᵉ itsᵉ
[suspension](synthetic-homotopy-theory.suspensions-of-types.mdᵉ) isᵉ
[`1`-connected](foundation.connected-types.md).ᵉ

Weᵉ canᵉ characterizeᵉ theᵉ `1`-acyclicᵉ typesᵉ asᵉ theᵉ
[`0`-connectedᵉ types](foundation.0-connected-types.md).ᵉ

Inᵉ oneᵉ direction,ᵉ ourᵉ proofᵉ reliesᵉ onᵉ theᵉ followingᵉ group-theoreticᵉ factᵉ: theᵉ
mapᵉ ofᵉ [generators](group-theory.generating-elements-groups.mdᵉ) fromᵉ aᵉ
[set](foundation-core.sets.mdᵉ) `X`ᵉ to theᵉ freeᵉ groupᵉ onᵉ `X`ᵉ isᵉ
[injective](foundation-core.injective-maps.md).ᵉ Thisᵉ isᵉ provedᵉ constructivelyᵉ in
{{#citeᵉ MRR88ᵉ}} byᵉ Mines,ᵉ Richmanᵉ andᵉ Ruitenburg,ᵉ andᵉ carriedᵉ outᵉ in HoTT/UFᵉ andᵉ
formalizedᵉ in Agdaᵉ in {{#citeᵉ BCDE21ᵉ}} byᵉ Bezem,ᵉ Coquand,ᵉ Dybjer,ᵉ andᵉ Escardó.ᵉ

Translatedᵉ to [concreteᵉ groups](group-theory.concrete-groups.mdᵉ) thisᵉ meansᵉ thatᵉ
forᵉ everyᵉ setᵉ `X`,ᵉ weᵉ haveᵉ aᵉ [pointed](structured-types.pointed-types.mdᵉ)
[`1`-type](foundation-core.1-types.mdᵉ) `ptᵉ : BG`ᵉ togetherᵉ with anᵉ injectionᵉ
`genᵉ : Xᵉ → ptᵉ ＝ᵉ pt`.ᵉ (Actually,ᵉ `BG`ᵉ isᵉ `0`-connectedᵉ asᵉ well,ᵉ butᵉ weᵉ don'tᵉ useᵉ
thisᵉ in ourᵉ proofᵉ below.ᵉ)

Aᵉ constructionᵉ onᵉ theᵉ levelᵉ ofᵉ concreteᵉ groupsᵉ canᵉ beᵉ foundᵉ in theᵉ recentᵉ
preprintᵉ byᵉ Davidᵉ Wärnᵉ {{#citeᵉ Warn23draft}}.ᵉ

Forᵉ theᵉ timeᵉ being,ᵉ weᵉ haven'tᵉ formalizedᵉ thisᵉ group-theoreticᵉ fact;ᵉ insteadᵉ weᵉ
labelᵉ itᵉ asᵉ anᵉ explicitᵉ assumptionᵉ ofᵉ ourᵉ proof.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  is-1-acyclic-Propᵉ : Propᵉ lᵉ
  is-1-acyclic-Propᵉ = is-truncated-acyclic-Propᵉ (one-𝕋ᵉ) Aᵉ

  is-1-acyclicᵉ : UUᵉ lᵉ
  is-1-acyclicᵉ = type-Propᵉ is-1-acyclic-Propᵉ

  is-prop-is-1-acyclicᵉ : is-propᵉ is-1-acyclicᵉ
  is-prop-is-1-acyclicᵉ = is-prop-type-Propᵉ is-1-acyclic-Propᵉ
```

## Properties

### Every `0`-connected type is `1`-acyclic

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  is-1-acyclic-is-0-connectedᵉ : is-0-connectedᵉ Aᵉ → is-1-acyclicᵉ Aᵉ
  is-1-acyclic-is-0-connectedᵉ = is-truncated-acyclic-succ-is-connectedᵉ
```

### Every `1`-acyclic type is `0`-connected

Asᵉ explainedᵉ atᵉ theᵉ topᵉ "Idea"ᵉ section,ᵉ weᵉ turnᵉ theᵉ necessaryᵉ group-theoreticᵉ
factᵉ intoᵉ anᵉ explicitᵉ assumptionᵉ ofᵉ ourᵉ proof.ᵉ

```agda
private
  record
    concrete-group-assumption'ᵉ {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) : UUᵉ (lsuc lᵉ)
    where
    field
      BGᵉ : Truncated-Typeᵉ lᵉ (one-𝕋ᵉ)
      ptᵉ : type-Truncated-Typeᵉ BGᵉ
      genᵉ : Aᵉ → type-Ωᵉ (pairᵉ (type-Truncated-Typeᵉ BGᵉ) ptᵉ)
      is-injective-genᵉ : is-injectiveᵉ genᵉ

  concrete-group-assumptionᵉ : UUωᵉ
  concrete-group-assumptionᵉ =
    {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → concrete-group-assumption'ᵉ Aᵉ

module _
  (cgaᵉ : concrete-group-assumptionᵉ)
  where

  is-contr-is-1-acyclic-is-setᵉ :
    {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) →
    is-setᵉ Aᵉ → is-1-acyclicᵉ Aᵉ → is-contrᵉ Aᵉ
  is-contr-is-1-acyclic-is-setᵉ Aᵉ sᵉ acᵉ =
    let open concrete-group-assumption'ᵉ (cgaᵉ Aᵉ) in
    is-contr-is-inhabited-is-propᵉ
      ( is-prop-all-elements-equalᵉ
        ( λ xᵉ yᵉ →
          is-injective-genᵉ
            ( binary-trᵉ
              ( Idᵉ)
              ( htpy-eqᵉ
                ( is-section-map-inv-equivᵉ
                  ( ( diagonal-exponentialᵉ
                      ( type-Ωᵉ (type-Truncated-Typeᵉ BGᵉ ,ᵉ ptᵉ))
                      ( Aᵉ)) ,ᵉ
                    ( is-equiv-diagonal-exponential-Id-is-acyclic-Truncated-Typeᵉ
                      ( Aᵉ)
                      ( acᵉ)
                      ( BGᵉ)
                      ( ptᵉ)
                      ( ptᵉ)))
                  ( genᵉ))
                ( xᵉ))
              ( htpy-eqᵉ
                ( is-section-map-inv-equivᵉ
                  ( ( diagonal-exponentialᵉ
                      ( type-Ωᵉ (type-Truncated-Typeᵉ BGᵉ ,ᵉ ptᵉ))
                      ( Aᵉ)) ,ᵉ
                    ( is-equiv-diagonal-exponential-Id-is-acyclic-Truncated-Typeᵉ
                      ( Aᵉ)
                      ( acᵉ)
                      ( BGᵉ)
                      ( ptᵉ)
                      ( ptᵉ)))
                  ( genᵉ))
                ( yᵉ))
              ( reflᵉ))))
      ( is-inhabited-is-0-acyclicᵉ
        ( is-truncated-acyclic-is-truncated-acyclic-succᵉ acᵉ))

  is-0-connected-is-1-acyclicᵉ :
    {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) →
    is-1-acyclicᵉ Aᵉ → is-0-connectedᵉ Aᵉ
  is-0-connected-is-1-acyclicᵉ Aᵉ acᵉ =
    is-contr-is-1-acyclic-is-setᵉ
      ( type-trunc-Setᵉ Aᵉ)
      ( is-set-type-trunc-Setᵉ)
      ( is-truncated-acyclic-succ-type-trunc-is-truncated-acyclic-succᵉ Aᵉ acᵉ)
```

## References

{{#bibliographyᵉ}}

## See also

-ᵉ [`k`-acyclicᵉ types](synthetic-homotopy-theory.truncated-acyclic-maps.mdᵉ)
-ᵉ [Acyclicᵉ types](synthetic-homotopy-theory.acyclic-types.mdᵉ)