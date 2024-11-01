# Torsorial type families

<pre class="Agda"><a id="36" class="Keyword">module</a> <a id="43" href="foundation-core.torsorial-type-families.html" class="Module">foundation-core.torsorial-type-families</a> <a id="83" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="139" class="Keyword">open</a> <a id="144" class="Keyword">import</a> <a id="151" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="183" class="Keyword">open</a> <a id="188" class="Keyword">import</a> <a id="195" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="223" class="Keyword">open</a> <a id="228" class="Keyword">import</a> <a id="235" href="foundation-core.contractible-types.html" class="Module">foundation-core.contractible-types</a>
<a id="270" class="Keyword">open</a> <a id="275" class="Keyword">import</a> <a id="282" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
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

<pre class="Agda"><a id="is-torsorial"></a><a id="2474" href="foundation-core.torsorial-type-families.html#2474" class="Function">is-torsorial</a> <a id="2487" class="Symbol">:</a>
  <a id="2491" class="Symbol">{</a><a id="2492" href="foundation-core.torsorial-type-families.html#2492" class="Bound">l1</a> <a id="2495" href="foundation-core.torsorial-type-families.html#2495" class="Bound">l2</a> <a id="2498" class="Symbol">:</a> <a id="2500" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2505" class="Symbol">}</a> <a id="2507" class="Symbol">{</a><a id="2508" href="foundation-core.torsorial-type-families.html#2508" class="Bound">B</a> <a id="2510" class="Symbol">:</a> <a id="2512" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2515" href="foundation-core.torsorial-type-families.html#2492" class="Bound">l1</a><a id="2517" class="Symbol">}</a> <a id="2519" class="Symbol">→</a> <a id="2521" class="Symbol">(</a><a id="2522" href="foundation-core.torsorial-type-families.html#2508" class="Bound">B</a> <a id="2524" class="Symbol">→</a> <a id="2526" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2529" href="foundation-core.torsorial-type-families.html#2495" class="Bound">l2</a><a id="2531" class="Symbol">)</a> <a id="2533" class="Symbol">→</a> <a id="2535" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2538" class="Symbol">(</a><a id="2539" href="foundation-core.torsorial-type-families.html#2492" class="Bound">l1</a> <a id="2542" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2544" href="foundation-core.torsorial-type-families.html#2495" class="Bound">l2</a><a id="2546" class="Symbol">)</a>
<a id="2548" href="foundation-core.torsorial-type-families.html#2474" class="Function">is-torsorial</a> <a id="2561" href="foundation-core.torsorial-type-families.html#2561" class="Bound">E</a> <a id="2563" class="Symbol">=</a> <a id="2565" href="foundation-core.contractible-types.html#894" class="Function">is-contr</a> <a id="2574" class="Symbol">(</a><a id="2575" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2577" class="Symbol">_</a> <a id="2579" href="foundation-core.torsorial-type-families.html#2561" class="Bound">E</a><a id="2580" class="Symbol">)</a>
</pre>
## Examples

### Identity types are torsorial

We prove two variants of the claim that
[identity types](foundation-core.identity-types.md) are torsorial:

- The type family `x ↦ a ＝ x` is torsorial, and
- The type family `x ↦ x ＝ a` is torsorial.

<pre class="Agda"><a id="2843" class="Keyword">module</a> <a id="2850" href="foundation-core.torsorial-type-families.html#2850" class="Module">_</a>
  <a id="2854" class="Symbol">{</a><a id="2855" href="foundation-core.torsorial-type-families.html#2855" class="Bound">l</a> <a id="2857" class="Symbol">:</a> <a id="2859" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2864" class="Symbol">}</a> <a id="2866" class="Symbol">{</a><a id="2867" href="foundation-core.torsorial-type-families.html#2867" class="Bound">A</a> <a id="2869" class="Symbol">:</a> <a id="2871" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2874" href="foundation-core.torsorial-type-families.html#2855" class="Bound">l</a><a id="2875" class="Symbol">}</a>
  <a id="2879" class="Keyword">where</a>

  <a id="2888" class="Keyword">abstract</a>
    <a id="2901" href="foundation-core.torsorial-type-families.html#2901" class="Function">is-torsorial-Id</a> <a id="2917" class="Symbol">:</a> <a id="2919" class="Symbol">(</a><a id="2920" href="foundation-core.torsorial-type-families.html#2920" class="Bound">a</a> <a id="2922" class="Symbol">:</a> <a id="2924" href="foundation-core.torsorial-type-families.html#2867" class="Bound">A</a><a id="2925" class="Symbol">)</a> <a id="2927" class="Symbol">→</a> <a id="2929" href="foundation-core.torsorial-type-families.html#2474" class="Function">is-torsorial</a> <a id="2942" class="Symbol">(λ</a> <a id="2945" href="foundation-core.torsorial-type-families.html#2945" class="Bound">x</a> <a id="2947" class="Symbol">→</a> <a id="2949" href="foundation-core.torsorial-type-families.html#2920" class="Bound">a</a> <a id="2951" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="2953" href="foundation-core.torsorial-type-families.html#2945" class="Bound">x</a><a id="2954" class="Symbol">)</a>
    <a id="2960" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2964" class="Symbol">(</a><a id="2965" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="2969" class="Symbol">(</a><a id="2970" href="foundation-core.torsorial-type-families.html#2901" class="Function">is-torsorial-Id</a> <a id="2986" href="foundation-core.torsorial-type-families.html#2986" class="Bound">a</a><a id="2987" class="Symbol">))</a> <a id="2990" class="Symbol">=</a> <a id="2992" href="foundation-core.torsorial-type-families.html#2986" class="Bound">a</a>
    <a id="2998" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3002" class="Symbol">(</a><a id="3003" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3007" class="Symbol">(</a><a id="3008" href="foundation-core.torsorial-type-families.html#2901" class="Function">is-torsorial-Id</a> <a id="3024" href="foundation-core.torsorial-type-families.html#3024" class="Bound">a</a><a id="3025" class="Symbol">))</a> <a id="3028" class="Symbol">=</a> <a id="3030" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
    <a id="3039" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3043" class="Symbol">(</a><a id="3044" href="foundation-core.torsorial-type-families.html#2901" class="Function">is-torsorial-Id</a> <a id="3060" href="foundation-core.torsorial-type-families.html#3060" class="Bound">a</a><a id="3061" class="Symbol">)</a> <a id="3063" class="Symbol">(</a><a id="3064" class="DottedPattern Symbol">.</a><a id="3065" href="foundation-core.torsorial-type-families.html#3060" class="DottedPattern Bound">a</a> <a id="3067" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3069" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="3073" class="Symbol">)</a> <a id="3075" class="Symbol">=</a> <a id="3077" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>

  <a id="3085" class="Keyword">abstract</a>
    <a id="3098" href="foundation-core.torsorial-type-families.html#3098" class="Function">is-torsorial-Id&#39;</a> <a id="3115" class="Symbol">:</a> <a id="3117" class="Symbol">(</a><a id="3118" href="foundation-core.torsorial-type-families.html#3118" class="Bound">a</a> <a id="3120" class="Symbol">:</a> <a id="3122" href="foundation-core.torsorial-type-families.html#2867" class="Bound">A</a><a id="3123" class="Symbol">)</a> <a id="3125" class="Symbol">→</a> <a id="3127" href="foundation-core.torsorial-type-families.html#2474" class="Function">is-torsorial</a> <a id="3140" class="Symbol">(λ</a> <a id="3143" href="foundation-core.torsorial-type-families.html#3143" class="Bound">x</a> <a id="3145" class="Symbol">→</a> <a id="3147" href="foundation-core.torsorial-type-families.html#3143" class="Bound">x</a> <a id="3149" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="3151" href="foundation-core.torsorial-type-families.html#3118" class="Bound">a</a><a id="3152" class="Symbol">)</a>
    <a id="3158" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3162" class="Symbol">(</a><a id="3163" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3167" class="Symbol">(</a><a id="3168" href="foundation-core.torsorial-type-families.html#3098" class="Function">is-torsorial-Id&#39;</a> <a id="3185" href="foundation-core.torsorial-type-families.html#3185" class="Bound">a</a><a id="3186" class="Symbol">))</a> <a id="3189" class="Symbol">=</a> <a id="3191" href="foundation-core.torsorial-type-families.html#3185" class="Bound">a</a>
    <a id="3197" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3201" class="Symbol">(</a><a id="3202" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="3206" class="Symbol">(</a><a id="3207" href="foundation-core.torsorial-type-families.html#3098" class="Function">is-torsorial-Id&#39;</a> <a id="3224" href="foundation-core.torsorial-type-families.html#3224" class="Bound">a</a><a id="3225" class="Symbol">))</a> <a id="3228" class="Symbol">=</a> <a id="3230" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
    <a id="3239" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="3243" class="Symbol">(</a><a id="3244" href="foundation-core.torsorial-type-families.html#3098" class="Function">is-torsorial-Id&#39;</a> <a id="3261" href="foundation-core.torsorial-type-families.html#3261" class="Bound">a</a><a id="3262" class="Symbol">)</a> <a id="3264" class="Symbol">(</a><a id="3265" class="DottedPattern Symbol">.</a><a id="3266" href="foundation-core.torsorial-type-families.html#3261" class="DottedPattern Bound">a</a> <a id="3268" href="foundation.dependent-pair-types.html#787" class="InductiveConstructor Operator">,</a> <a id="3270" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="3274" class="Symbol">)</a> <a id="3276" class="Symbol">=</a> <a id="3278" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>
### See also

- [Discrete relations](foundation.discrete-relations.md) are binary torsorial
  type families.
