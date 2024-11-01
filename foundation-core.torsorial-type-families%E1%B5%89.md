# Torsorial type families

<pre class="Agda"><a id="36" class="Keyword">module</a> <a id="43" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html" class="Module">foundation-core.torsorial-type-familiesᵉ</a> <a id="84" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="140" class="Keyword">open</a> <a id="145" class="Keyword">import</a> <a id="152" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="185" class="Keyword">open</a> <a id="190" class="Keyword">import</a> <a id="197" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="226" class="Keyword">open</a> <a id="231" class="Keyword">import</a> <a id="238" href="foundation-core.contractible-types%25E1%25B5%2589.html" class="Module">foundation-core.contractible-typesᵉ</a>
<a id="274" class="Keyword">open</a> <a id="279" class="Keyword">import</a> <a id="286" href="foundation-core.identity-types%25E1%25B5%2589.html" class="Module">foundation-core.identity-typesᵉ</a>
</pre>
</details>

## Idea

A type family `B` over `A` is said to be
{{#concept "torsorial" Disambiguation="type family" Agda=is-torsorial}} if its
[total space](foundation.dependent-pair-types.md) is
[contractible](foundation-core.contractible-types.md).

The terminology of torsorial type families is derived from torsors of
[higher group theory](higher-group-theory.md), which are type families
`X : BG → 𝒰` with contractible total space. In the conventional sense of the
word, a torsor is therefore a torsorial type family over a
[pointed connected type](higher-group-theory.higher-groups.md). If we drop the
condition that they are defined over a pointed connected type, we get to the
notion of 'torsor-like', or indeed 'torsorial' type families.

The notion of torsoriality of type families is central in many characterizations
of identity types. Indeed, the
[fundamental theorem of identity types](foundation.fundamental-theorem-of-identity-types.md)
shows that for any type family `B` over `A` and any `a : A`, the type family `B`
is torsorial if and only if every
[family of maps](foundation.families-of-maps.md)

```text
  (x : A) → a ＝ x → B x
```

is a [family of equivalences](foundation.families-of-equivalences.md). Indeed,
the principal example of a torsorial type family is the
[identity type](foundation-core.identity-types.md) itself. More generally, any
type family in the [connected component](foundation.connected-components.md) of
the identity type `x ↦ a ＝ x` is torsorial. These include torsors of higher
groups and [torsors](group-theory.torsors.md) of
[concrete groups](group-theory.concrete-groups.md).

Establishing torsoriality of type families is therefore one of the routine tasks
in univalent mathematics. Some files that provide general tools for establishing
torsoriality of type families include:

- [Equality of dependent function types](foundation.equality-dependent-function-types.md),
- The
  [structure identity principle](foundation.structure-identity-principle.md),
- The [subtype identity principle](foundation.subtype-identity-principle.md).

## Definition

### The predicate of being a torsorial type family

<pre class="Agda"><a id="is-torsorialᵉ"></a><a id="2479" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2479" class="Function">is-torsorialᵉ</a> <a id="2493" class="Symbol">:</a>
  <a id="2497" class="Symbol">{</a><a id="2498" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2498" class="Bound">l1ᵉ</a> <a id="2502" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2502" class="Bound">l2ᵉ</a> <a id="2506" class="Symbol">:</a> <a id="2508" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2513" class="Symbol">}</a> <a id="2515" class="Symbol">{</a><a id="2516" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2516" class="Bound">Bᵉ</a> <a id="2519" class="Symbol">:</a> <a id="2521" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2525" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2498" class="Bound">l1ᵉ</a><a id="2528" class="Symbol">}</a> <a id="2530" class="Symbol">→</a> <a id="2532" class="Symbol">(</a><a id="2533" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2516" class="Bound">Bᵉ</a> <a id="2536" class="Symbol">→</a> <a id="2538" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2542" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2502" class="Bound">l2ᵉ</a><a id="2545" class="Symbol">)</a> <a id="2547" class="Symbol">→</a> <a id="2549" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2553" class="Symbol">(</a><a id="2554" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2498" class="Bound">l1ᵉ</a> <a id="2558" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2560" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2502" class="Bound">l2ᵉ</a><a id="2563" class="Symbol">)</a>
<a id="2565" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2479" class="Function">is-torsorialᵉ</a> <a id="2579" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2579" class="Bound">Eᵉ</a> <a id="2582" class="Symbol">=</a> <a id="2584" href="foundation-core.contractible-types%25E1%25B5%2589.html#908" class="Function">is-contrᵉ</a> <a id="2594" class="Symbol">(</a><a id="2595" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="2598" class="Symbol">_</a> <a id="2600" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2579" class="Bound">Eᵉ</a><a id="2602" class="Symbol">)</a>
</pre>
## Examples

### Identity types are torsorial

We prove two variants of the claim that
[identity types](foundation-core.identity-types.md) are torsorial:

- The type family `x ↦ a ＝ x` is torsorial, and
- The type family `x ↦ x ＝ a` is torsorial.

<pre class="Agda"><a id="2865" class="Keyword">module</a> <a id="2872" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2872" class="Module">_</a>
  <a id="2876" class="Symbol">{</a><a id="2877" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2877" class="Bound">lᵉ</a> <a id="2880" class="Symbol">:</a> <a id="2882" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2887" class="Symbol">}</a> <a id="2889" class="Symbol">{</a><a id="2890" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2890" class="Bound">Aᵉ</a> <a id="2893" class="Symbol">:</a> <a id="2895" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2899" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2877" class="Bound">lᵉ</a><a id="2901" class="Symbol">}</a>
  <a id="2905" class="Keyword">where</a>

  <a id="2914" class="Keyword">abstract</a>
    <a id="2927" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2927" class="Function">is-torsorial-Idᵉ</a> <a id="2944" class="Symbol">:</a> <a id="2946" class="Symbol">(</a><a id="2947" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2947" class="Bound">aᵉ</a> <a id="2950" class="Symbol">:</a> <a id="2952" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2890" class="Bound">Aᵉ</a><a id="2954" class="Symbol">)</a> <a id="2956" class="Symbol">→</a> <a id="2958" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2479" class="Function">is-torsorialᵉ</a> <a id="2972" class="Symbol">(λ</a> <a id="2975" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2975" class="Bound">xᵉ</a> <a id="2978" class="Symbol">→</a> <a id="2980" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2947" class="Bound">aᵉ</a> <a id="2983" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="2986" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2975" class="Bound">xᵉ</a><a id="2988" class="Symbol">)</a>
    <a id="2994" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="2999" class="Symbol">(</a><a id="3000" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="3005" class="Symbol">(</a><a id="3006" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2927" class="Function">is-torsorial-Idᵉ</a> <a id="3023" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#3023" class="Bound">aᵉ</a><a id="3025" class="Symbol">))</a> <a id="3028" class="Symbol">=</a> <a id="3030" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#3023" class="Bound">aᵉ</a>
    <a id="3037" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="3042" class="Symbol">(</a><a id="3043" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="3048" class="Symbol">(</a><a id="3049" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2927" class="Function">is-torsorial-Idᵉ</a> <a id="3066" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#3066" class="Bound">aᵉ</a><a id="3068" class="Symbol">))</a> <a id="3071" class="Symbol">=</a> <a id="3073" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a>
    <a id="3083" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="3088" class="Symbol">(</a><a id="3089" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2927" class="Function">is-torsorial-Idᵉ</a> <a id="3106" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#3106" class="Bound">aᵉ</a><a id="3108" class="Symbol">)</a> <a id="3110" class="Symbol">(</a><a id="3111" class="DottedPattern Symbol">.</a><a id="3112" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#3106" class="DottedPattern Bound">aᵉ</a> <a id="3115" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="3118" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a><a id="3123" class="Symbol">)</a> <a id="3125" class="Symbol">=</a> <a id="3127" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a>

  <a id="3136" class="Keyword">abstract</a>
    <a id="3149" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#3149" class="Function">is-torsorial-Id&#39;ᵉ</a> <a id="3167" class="Symbol">:</a> <a id="3169" class="Symbol">(</a><a id="3170" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#3170" class="Bound">aᵉ</a> <a id="3173" class="Symbol">:</a> <a id="3175" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2890" class="Bound">Aᵉ</a><a id="3177" class="Symbol">)</a> <a id="3179" class="Symbol">→</a> <a id="3181" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#2479" class="Function">is-torsorialᵉ</a> <a id="3195" class="Symbol">(λ</a> <a id="3198" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#3198" class="Bound">xᵉ</a> <a id="3201" class="Symbol">→</a> <a id="3203" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#3198" class="Bound">xᵉ</a> <a id="3206" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="3209" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#3170" class="Bound">aᵉ</a><a id="3211" class="Symbol">)</a>
    <a id="3217" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="3222" class="Symbol">(</a><a id="3223" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="3228" class="Symbol">(</a><a id="3229" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#3149" class="Function">is-torsorial-Id&#39;ᵉ</a> <a id="3247" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#3247" class="Bound">aᵉ</a><a id="3249" class="Symbol">))</a> <a id="3252" class="Symbol">=</a> <a id="3254" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#3247" class="Bound">aᵉ</a>
    <a id="3261" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="3266" class="Symbol">(</a><a id="3267" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="3272" class="Symbol">(</a><a id="3273" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#3149" class="Function">is-torsorial-Id&#39;ᵉ</a> <a id="3291" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#3291" class="Bound">aᵉ</a><a id="3293" class="Symbol">))</a> <a id="3296" class="Symbol">=</a> <a id="3298" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a>
    <a id="3308" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="3313" class="Symbol">(</a><a id="3314" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#3149" class="Function">is-torsorial-Id&#39;ᵉ</a> <a id="3332" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#3332" class="Bound">aᵉ</a><a id="3334" class="Symbol">)</a> <a id="3336" class="Symbol">(</a><a id="3337" class="DottedPattern Symbol">.</a><a id="3338" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html#3332" class="DottedPattern Bound">aᵉ</a> <a id="3341" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="3344" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a><a id="3349" class="Symbol">)</a> <a id="3351" class="Symbol">=</a> <a id="3353" href="foundation-core.identity-types%25E1%25B5%2589.html#2694" class="InductiveConstructor">reflᵉ</a>
</pre>
### See also

- [Discrete relations](foundation.discrete-relations.md) are binary torsorial
  type families.