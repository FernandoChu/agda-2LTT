# Wild monoids

<pre class="Agda"><a id="25" class="Keyword">module</a> <a id="32" href="structured-types.wild-monoids%25E1%25B5%2589.html" class="Module">structured-types.wild-monoidsᵉ</a> <a id="63" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="119" class="Keyword">open</a> <a id="124" class="Keyword">import</a> <a id="131" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html" class="Module">foundation.action-on-identifications-functionsᵉ</a>
<a id="179" class="Keyword">open</a> <a id="184" class="Keyword">import</a> <a id="191" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="224" class="Keyword">open</a> <a id="229" class="Keyword">import</a> <a id="236" href="foundation.identity-types%25E1%25B5%2589.html" class="Module">foundation.identity-typesᵉ</a>
<a id="263" class="Keyword">open</a> <a id="268" class="Keyword">import</a> <a id="275" href="foundation.unit-type%25E1%25B5%2589.html" class="Module">foundation.unit-typeᵉ</a>
<a id="297" class="Keyword">open</a> <a id="302" class="Keyword">import</a> <a id="309" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="338" class="Keyword">open</a> <a id="343" class="Keyword">import</a> <a id="350" href="structured-types.h-spaces%25E1%25B5%2589.html" class="Module">structured-types.h-spacesᵉ</a>
<a id="377" class="Keyword">open</a> <a id="382" class="Keyword">import</a> <a id="389" href="structured-types.pointed-types%25E1%25B5%2589.html" class="Module">structured-types.pointed-typesᵉ</a>
</pre>
</details>

## Idea

A **wild monoid** is a first–order approximation to an ∞-monoid, i.e. a
∞-monoid-like structure whose laws hold at least up to the first homotopy level,
but may fail at higher levels.

A wild monoid consists of

- an underlying type `A`
- a unit, say `e : A`
- a binary operation on `A`, say `_*_`
- left and right unit laws `e * x ＝ x` and `x * e ＝ x`
- a coherence between the left and right unit laws at the unit
- an associator `(x y z : A) → (x * y) * z ＝ x * (y * z)`
- coherences between the associator and the left and right unit laws

We call such an associator **unital**. It may be described as a coherence of the
following diagram

```text
          map-associative-product
     (A × A) × A ----> A × (A × A)
             |           |
  (_*_ , id) |           | (id, _*_)
             ∨           ∨
           A × A       A × A
               \       /
          (_*_) \     / (_*_)
                 ∨   ∨
                   A
```

such that the three diagrams below cohere

```text
            associator
  (e * x) * y ===== e * (x * y)
          \\         //
     left  \\       //  left
   unit law \\     // unit law
              y * z,
```

```text
            associator
  (x * e) * y ===== x * (e * y)
          \\         //
    right  \\       //  left
   unit law \\     // unit law
              x * y,
```

and

```text
            associator
  (x * y) * e ===== x * (y * e)
          \\         //
    right  \\       //  right
   unit law \\     // unit law
              x * y
```

for all `x y : A`.

Concretely, we define wild monoids to be
[H-spaces](structured-types.h-spaces.md) equipped with a unital associator.

## Definition

### Unital associators on H-spaces

<pre class="Agda"><a id="2156" class="Keyword">module</a> <a id="2163" href="structured-types.wild-monoids%25E1%25B5%2589.html#2163" class="Module">_</a>
  <a id="2167" class="Symbol">{</a><a id="2168" href="structured-types.wild-monoids%25E1%25B5%2589.html#2168" class="Bound">lᵉ</a> <a id="2171" class="Symbol">:</a> <a id="2173" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2178" class="Symbol">}</a> <a id="2180" class="Symbol">(</a><a id="2181" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a> <a id="2184" class="Symbol">:</a> <a id="2186" href="structured-types.h-spaces%25E1%25B5%2589.html#2553" class="Function">H-Spaceᵉ</a> <a id="2195" href="structured-types.wild-monoids%25E1%25B5%2589.html#2168" class="Bound">lᵉ</a><a id="2197" class="Symbol">)</a>
  <a id="2201" class="Keyword">where</a>

  <a id="2210" href="structured-types.wild-monoids%25E1%25B5%2589.html#2210" class="Function">associator-H-Spaceᵉ</a> <a id="2230" class="Symbol">:</a> <a id="2232" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2236" href="structured-types.wild-monoids%25E1%25B5%2589.html#2168" class="Bound">lᵉ</a>
  <a id="2241" href="structured-types.wild-monoids%25E1%25B5%2589.html#2210" class="Function">associator-H-Spaceᵉ</a> <a id="2261" class="Symbol">=</a>
    <a id="2267" class="Symbol">(</a><a id="2268" href="structured-types.wild-monoids%25E1%25B5%2589.html#2268" class="Bound">xᵉ</a> <a id="2271" href="structured-types.wild-monoids%25E1%25B5%2589.html#2271" class="Bound">yᵉ</a> <a id="2274" href="structured-types.wild-monoids%25E1%25B5%2589.html#2274" class="Bound">zᵉ</a> <a id="2277" class="Symbol">:</a> <a id="2279" href="structured-types.h-spaces%25E1%25B5%2589.html#2975" class="Function">type-H-Spaceᵉ</a> <a id="2293" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a><a id="2295" class="Symbol">)</a> <a id="2297" class="Symbol">→</a>
    <a id="2303" href="foundation-core.identity-types%25E1%25B5%2589.html#2647" class="Datatype">Idᵉ</a>
      <a id="2313" class="Symbol">(</a> <a id="2315" href="structured-types.h-spaces%25E1%25B5%2589.html#3288" class="Function">mul-H-Spaceᵉ</a> <a id="2328" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a> <a id="2331" class="Symbol">(</a><a id="2332" href="structured-types.h-spaces%25E1%25B5%2589.html#3288" class="Function">mul-H-Spaceᵉ</a> <a id="2345" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a> <a id="2348" href="structured-types.wild-monoids%25E1%25B5%2589.html#2268" class="Bound">xᵉ</a> <a id="2351" href="structured-types.wild-monoids%25E1%25B5%2589.html#2271" class="Bound">yᵉ</a><a id="2353" class="Symbol">)</a> <a id="2355" href="structured-types.wild-monoids%25E1%25B5%2589.html#2274" class="Bound">zᵉ</a><a id="2357" class="Symbol">)</a>
      <a id="2365" class="Symbol">(</a> <a id="2367" href="structured-types.h-spaces%25E1%25B5%2589.html#3288" class="Function">mul-H-Spaceᵉ</a> <a id="2380" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a> <a id="2383" href="structured-types.wild-monoids%25E1%25B5%2589.html#2268" class="Bound">xᵉ</a> <a id="2386" class="Symbol">(</a><a id="2387" href="structured-types.h-spaces%25E1%25B5%2589.html#3288" class="Function">mul-H-Spaceᵉ</a> <a id="2400" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a> <a id="2403" href="structured-types.wild-monoids%25E1%25B5%2589.html#2271" class="Bound">yᵉ</a> <a id="2406" href="structured-types.wild-monoids%25E1%25B5%2589.html#2274" class="Bound">zᵉ</a><a id="2408" class="Symbol">))</a>

  <a id="2414" href="structured-types.wild-monoids%25E1%25B5%2589.html#2414" class="Function">is-unital-associatorᵉ</a> <a id="2436" class="Symbol">:</a> <a id="2438" class="Symbol">(</a><a id="2439" href="structured-types.wild-monoids%25E1%25B5%2589.html#2439" class="Bound">αᵉ</a> <a id="2442" class="Symbol">:</a> <a id="2444" href="structured-types.wild-monoids%25E1%25B5%2589.html#2210" class="Function">associator-H-Spaceᵉ</a><a id="2463" class="Symbol">)</a> <a id="2465" class="Symbol">→</a> <a id="2467" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2471" href="structured-types.wild-monoids%25E1%25B5%2589.html#2168" class="Bound">lᵉ</a>
  <a id="2476" href="structured-types.wild-monoids%25E1%25B5%2589.html#2414" class="Function">is-unital-associatorᵉ</a> <a id="2498" href="structured-types.wild-monoids%25E1%25B5%2589.html#2498" class="Bound">α111ᵉ</a> <a id="2504" class="Symbol">=</a>
    <a id="2510" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="2513" class="Symbol">(</a> <a id="2515" class="Symbol">(</a><a id="2516" href="structured-types.wild-monoids%25E1%25B5%2589.html#2516" class="Bound">yᵉ</a> <a id="2519" href="structured-types.wild-monoids%25E1%25B5%2589.html#2519" class="Bound">zᵉ</a> <a id="2522" class="Symbol">:</a> <a id="2524" href="structured-types.h-spaces%25E1%25B5%2589.html#2975" class="Function">type-H-Spaceᵉ</a> <a id="2538" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a><a id="2540" class="Symbol">)</a> <a id="2542" class="Symbol">→</a>
        <a id="2552" href="foundation-core.identity-types%25E1%25B5%2589.html#2647" class="Datatype">Idᵉ</a>
          <a id="2566" class="Symbol">(</a> <a id="2568" class="Symbol">(</a> <a id="2570" href="structured-types.wild-monoids%25E1%25B5%2589.html#2498" class="Bound">α111ᵉ</a> <a id="2576" class="Symbol">(</a><a id="2577" href="structured-types.h-spaces%25E1%25B5%2589.html#3060" class="Function">unit-H-Spaceᵉ</a> <a id="2591" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a><a id="2593" class="Symbol">)</a> <a id="2595" href="structured-types.wild-monoids%25E1%25B5%2589.html#2516" class="Bound">yᵉ</a> <a id="2598" href="structured-types.wild-monoids%25E1%25B5%2589.html#2519" class="Bound">zᵉ</a><a id="2600" class="Symbol">)</a> <a id="2602" href="foundation-core.identity-types%25E1%25B5%2589.html#5906" class="Function Operator">∙ᵉ</a>
            <a id="2617" class="Symbol">(</a> <a id="2619" href="structured-types.h-spaces%25E1%25B5%2589.html#3973" class="Function">left-unit-law-mul-H-Spaceᵉ</a> <a id="2646" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a>
              <a id="2663" class="Symbol">(</a> <a id="2665" href="structured-types.h-spaces%25E1%25B5%2589.html#3288" class="Function">mul-H-Spaceᵉ</a> <a id="2678" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a> <a id="2681" href="structured-types.wild-monoids%25E1%25B5%2589.html#2516" class="Bound">yᵉ</a> <a id="2684" href="structured-types.wild-monoids%25E1%25B5%2589.html#2519" class="Bound">zᵉ</a><a id="2686" class="Symbol">)))</a>
            <a id="2702" class="Symbol">(</a> <a id="2704" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a>
              <a id="2722" class="Symbol">(</a> <a id="2724" href="structured-types.h-spaces%25E1%25B5%2589.html#3407" class="Function">mul-H-Space&#39;ᵉ</a> <a id="2738" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a> <a id="2741" href="structured-types.wild-monoids%25E1%25B5%2589.html#2519" class="Bound">zᵉ</a><a id="2743" class="Symbol">)</a>
              <a id="2759" class="Symbol">(</a> <a id="2761" href="structured-types.h-spaces%25E1%25B5%2589.html#3973" class="Function">left-unit-law-mul-H-Spaceᵉ</a> <a id="2788" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a> <a id="2791" href="structured-types.wild-monoids%25E1%25B5%2589.html#2516" class="Bound">yᵉ</a><a id="2793" class="Symbol">)))</a>
      <a id="2803" class="Symbol">(</a> <a id="2805" class="Symbol">λ</a> <a id="2807" href="structured-types.wild-monoids%25E1%25B5%2589.html#2807" class="Bound">α011ᵉ</a> <a id="2813" class="Symbol">→</a>
        <a id="2823" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="2826" class="Symbol">(</a> <a id="2828" class="Symbol">(</a><a id="2829" href="structured-types.wild-monoids%25E1%25B5%2589.html#2829" class="Bound">xᵉ</a> <a id="2832" href="structured-types.wild-monoids%25E1%25B5%2589.html#2832" class="Bound">zᵉ</a> <a id="2835" class="Symbol">:</a> <a id="2837" href="structured-types.h-spaces%25E1%25B5%2589.html#2975" class="Function">type-H-Spaceᵉ</a> <a id="2851" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a><a id="2853" class="Symbol">)</a> <a id="2855" class="Symbol">→</a>
            <a id="2869" href="foundation-core.identity-types%25E1%25B5%2589.html#2647" class="Datatype">Idᵉ</a>
              <a id="2887" class="Symbol">(</a> <a id="2889" class="Symbol">(</a> <a id="2891" href="structured-types.wild-monoids%25E1%25B5%2589.html#2498" class="Bound">α111ᵉ</a> <a id="2897" href="structured-types.wild-monoids%25E1%25B5%2589.html#2829" class="Bound">xᵉ</a> <a id="2900" class="Symbol">(</a><a id="2901" href="structured-types.h-spaces%25E1%25B5%2589.html#3060" class="Function">unit-H-Spaceᵉ</a> <a id="2915" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a><a id="2917" class="Symbol">)</a> <a id="2919" href="structured-types.wild-monoids%25E1%25B5%2589.html#2832" class="Bound">zᵉ</a><a id="2921" class="Symbol">)</a> <a id="2923" href="foundation-core.identity-types%25E1%25B5%2589.html#5906" class="Function Operator">∙ᵉ</a>
                <a id="2942" class="Symbol">(</a> <a id="2944" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a>
                  <a id="2966" class="Symbol">(</a> <a id="2968" href="structured-types.h-spaces%25E1%25B5%2589.html#3288" class="Function">mul-H-Spaceᵉ</a> <a id="2981" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a> <a id="2984" href="structured-types.wild-monoids%25E1%25B5%2589.html#2829" class="Bound">xᵉ</a><a id="2986" class="Symbol">)</a>
                  <a id="3006" class="Symbol">(</a> <a id="3008" href="structured-types.h-spaces%25E1%25B5%2589.html#3973" class="Function">left-unit-law-mul-H-Spaceᵉ</a> <a id="3035" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a> <a id="3038" href="structured-types.wild-monoids%25E1%25B5%2589.html#2832" class="Bound">zᵉ</a><a id="3040" class="Symbol">)))</a>
              <a id="3058" class="Symbol">(</a> <a id="3060" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a>
                <a id="3080" class="Symbol">(</a> <a id="3082" href="structured-types.h-spaces%25E1%25B5%2589.html#3407" class="Function">mul-H-Space&#39;ᵉ</a> <a id="3096" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a> <a id="3099" href="structured-types.wild-monoids%25E1%25B5%2589.html#2832" class="Bound">zᵉ</a><a id="3101" class="Symbol">)</a>
                <a id="3119" class="Symbol">(</a> <a id="3121" href="structured-types.h-spaces%25E1%25B5%2589.html#4147" class="Function">right-unit-law-mul-H-Spaceᵉ</a> <a id="3149" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a> <a id="3152" href="structured-types.wild-monoids%25E1%25B5%2589.html#2829" class="Bound">xᵉ</a><a id="3154" class="Symbol">)))</a>
          <a id="3168" class="Symbol">(</a> <a id="3170" class="Symbol">λ</a> <a id="3172" href="structured-types.wild-monoids%25E1%25B5%2589.html#3172" class="Bound">α101ᵉ</a> <a id="3178" class="Symbol">→</a>
            <a id="3192" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="3195" class="Symbol">(</a> <a id="3197" class="Symbol">(</a><a id="3198" href="structured-types.wild-monoids%25E1%25B5%2589.html#3198" class="Bound">xᵉ</a> <a id="3201" href="structured-types.wild-monoids%25E1%25B5%2589.html#3201" class="Bound">yᵉ</a> <a id="3204" class="Symbol">:</a> <a id="3206" href="structured-types.h-spaces%25E1%25B5%2589.html#2975" class="Function">type-H-Spaceᵉ</a> <a id="3220" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a><a id="3222" class="Symbol">)</a> <a id="3224" class="Symbol">→</a>
                <a id="3242" href="foundation-core.identity-types%25E1%25B5%2589.html#2647" class="Datatype">Idᵉ</a>
                  <a id="3264" class="Symbol">(</a> <a id="3266" class="Symbol">(</a> <a id="3268" href="structured-types.wild-monoids%25E1%25B5%2589.html#2498" class="Bound">α111ᵉ</a> <a id="3274" href="structured-types.wild-monoids%25E1%25B5%2589.html#3198" class="Bound">xᵉ</a> <a id="3277" href="structured-types.wild-monoids%25E1%25B5%2589.html#3201" class="Bound">yᵉ</a> <a id="3280" class="Symbol">(</a><a id="3281" href="structured-types.h-spaces%25E1%25B5%2589.html#3060" class="Function">unit-H-Spaceᵉ</a> <a id="3295" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a><a id="3297" class="Symbol">))</a> <a id="3300" href="foundation-core.identity-types%25E1%25B5%2589.html#5906" class="Function Operator">∙ᵉ</a>
                    <a id="3323" class="Symbol">(</a> <a id="3325" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a>
                      <a id="3351" class="Symbol">(</a> <a id="3353" href="structured-types.h-spaces%25E1%25B5%2589.html#3288" class="Function">mul-H-Spaceᵉ</a> <a id="3366" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a> <a id="3369" href="structured-types.wild-monoids%25E1%25B5%2589.html#3198" class="Bound">xᵉ</a><a id="3371" class="Symbol">)</a>
                      <a id="3395" class="Symbol">(</a> <a id="3397" href="structured-types.h-spaces%25E1%25B5%2589.html#4147" class="Function">right-unit-law-mul-H-Spaceᵉ</a> <a id="3425" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a> <a id="3428" href="structured-types.wild-monoids%25E1%25B5%2589.html#3201" class="Bound">yᵉ</a><a id="3430" class="Symbol">)))</a>
                  <a id="3452" class="Symbol">(</a> <a id="3454" href="structured-types.h-spaces%25E1%25B5%2589.html#4147" class="Function">right-unit-law-mul-H-Spaceᵉ</a> <a id="3482" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a>
                    <a id="3505" class="Symbol">(</a> <a id="3507" href="structured-types.h-spaces%25E1%25B5%2589.html#3288" class="Function">mul-H-Spaceᵉ</a> <a id="3520" href="structured-types.wild-monoids%25E1%25B5%2589.html#2181" class="Bound">Mᵉ</a> <a id="3523" href="structured-types.wild-monoids%25E1%25B5%2589.html#3198" class="Bound">xᵉ</a> <a id="3526" href="structured-types.wild-monoids%25E1%25B5%2589.html#3201" class="Bound">yᵉ</a><a id="3528" class="Symbol">)))</a>
              <a id="3546" class="Symbol">(</a> <a id="3548" class="Symbol">λ</a> <a id="3550" href="structured-types.wild-monoids%25E1%25B5%2589.html#3550" class="Bound">α110ᵉ</a> <a id="3556" class="Symbol">→</a> <a id="3558" href="foundation.unit-type%25E1%25B5%2589.html#826" class="Record">unitᵉ</a><a id="3563" class="Symbol">)))</a>

  <a id="3570" href="structured-types.wild-monoids%25E1%25B5%2589.html#3570" class="Function">unital-associatorᵉ</a> <a id="3589" class="Symbol">:</a> <a id="3591" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="3595" href="structured-types.wild-monoids%25E1%25B5%2589.html#2168" class="Bound">lᵉ</a>
  <a id="3600" href="structured-types.wild-monoids%25E1%25B5%2589.html#3570" class="Function">unital-associatorᵉ</a> <a id="3619" class="Symbol">=</a> <a id="3621" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="3624" class="Symbol">(</a><a id="3625" href="structured-types.wild-monoids%25E1%25B5%2589.html#2210" class="Function">associator-H-Spaceᵉ</a><a id="3644" class="Symbol">)</a> <a id="3646" class="Symbol">(</a><a id="3647" href="structured-types.wild-monoids%25E1%25B5%2589.html#2414" class="Function">is-unital-associatorᵉ</a><a id="3668" class="Symbol">)</a>
</pre>
### Wild monoids

<pre class="Agda"><a id="Wild-Monoidᵉ"></a><a id="3701" href="structured-types.wild-monoids%25E1%25B5%2589.html#3701" class="Function">Wild-Monoidᵉ</a> <a id="3714" class="Symbol">:</a> <a id="3716" class="Symbol">(</a><a id="3717" href="structured-types.wild-monoids%25E1%25B5%2589.html#3717" class="Bound">lᵉ</a> <a id="3720" class="Symbol">:</a> <a id="3722" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3727" class="Symbol">)</a> <a id="3729" class="Symbol">→</a> <a id="3731" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="3735" class="Symbol">(</a><a id="3736" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="3741" href="structured-types.wild-monoids%25E1%25B5%2589.html#3717" class="Bound">lᵉ</a><a id="3743" class="Symbol">)</a>
<a id="3745" href="structured-types.wild-monoids%25E1%25B5%2589.html#3701" class="Function">Wild-Monoidᵉ</a> <a id="3758" href="structured-types.wild-monoids%25E1%25B5%2589.html#3758" class="Bound">lᵉ</a> <a id="3761" class="Symbol">=</a>
  <a id="3765" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="3768" class="Symbol">(</a><a id="3769" href="structured-types.h-spaces%25E1%25B5%2589.html#2553" class="Function">H-Spaceᵉ</a> <a id="3778" href="structured-types.wild-monoids%25E1%25B5%2589.html#3758" class="Bound">lᵉ</a><a id="3780" class="Symbol">)</a> <a id="3782" href="structured-types.wild-monoids%25E1%25B5%2589.html#3570" class="Function">unital-associatorᵉ</a>

<a id="3802" class="Keyword">module</a> <a id="3809" href="structured-types.wild-monoids%25E1%25B5%2589.html#3809" class="Module">_</a>
  <a id="3813" class="Symbol">{</a><a id="3814" href="structured-types.wild-monoids%25E1%25B5%2589.html#3814" class="Bound">lᵉ</a> <a id="3817" class="Symbol">:</a> <a id="3819" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3824" class="Symbol">}</a> <a id="3826" class="Symbol">(</a><a id="3827" href="structured-types.wild-monoids%25E1%25B5%2589.html#3827" class="Bound">Mᵉ</a> <a id="3830" class="Symbol">:</a> <a id="3832" href="structured-types.wild-monoids%25E1%25B5%2589.html#3701" class="Function">Wild-Monoidᵉ</a> <a id="3845" href="structured-types.wild-monoids%25E1%25B5%2589.html#3814" class="Bound">lᵉ</a><a id="3847" class="Symbol">)</a>
  <a id="3851" class="Keyword">where</a>

  <a id="3860" href="structured-types.wild-monoids%25E1%25B5%2589.html#3860" class="Function">h-space-Wild-Monoidᵉ</a> <a id="3881" class="Symbol">:</a> <a id="3883" href="structured-types.h-spaces%25E1%25B5%2589.html#2553" class="Function">H-Spaceᵉ</a> <a id="3892" href="structured-types.wild-monoids%25E1%25B5%2589.html#3814" class="Bound">lᵉ</a>
  <a id="3897" href="structured-types.wild-monoids%25E1%25B5%2589.html#3860" class="Function">h-space-Wild-Monoidᵉ</a> <a id="3918" class="Symbol">=</a> <a id="3920" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="3925" href="structured-types.wild-monoids%25E1%25B5%2589.html#3827" class="Bound">Mᵉ</a>

  <a id="3931" href="structured-types.wild-monoids%25E1%25B5%2589.html#3931" class="Function">type-Wild-Monoidᵉ</a> <a id="3949" class="Symbol">:</a> <a id="3951" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="3955" href="structured-types.wild-monoids%25E1%25B5%2589.html#3814" class="Bound">lᵉ</a>
  <a id="3960" href="structured-types.wild-monoids%25E1%25B5%2589.html#3931" class="Function">type-Wild-Monoidᵉ</a> <a id="3978" class="Symbol">=</a> <a id="3980" href="structured-types.h-spaces%25E1%25B5%2589.html#2975" class="Function">type-H-Spaceᵉ</a> <a id="3994" href="structured-types.wild-monoids%25E1%25B5%2589.html#3860" class="Function">h-space-Wild-Monoidᵉ</a>

  <a id="4018" href="structured-types.wild-monoids%25E1%25B5%2589.html#4018" class="Function">unit-Wild-Monoidᵉ</a> <a id="4036" class="Symbol">:</a> <a id="4038" href="structured-types.wild-monoids%25E1%25B5%2589.html#3931" class="Function">type-Wild-Monoidᵉ</a>
  <a id="4058" href="structured-types.wild-monoids%25E1%25B5%2589.html#4018" class="Function">unit-Wild-Monoidᵉ</a> <a id="4076" class="Symbol">=</a> <a id="4078" href="structured-types.h-spaces%25E1%25B5%2589.html#3060" class="Function">unit-H-Spaceᵉ</a> <a id="4092" href="structured-types.wild-monoids%25E1%25B5%2589.html#3860" class="Function">h-space-Wild-Monoidᵉ</a>

  <a id="4116" href="structured-types.wild-monoids%25E1%25B5%2589.html#4116" class="Function">pointed-type-Wild-Monoidᵉ</a> <a id="4142" class="Symbol">:</a> <a id="4144" href="structured-types.pointed-types%25E1%25B5%2589.html#358" class="Function">Pointed-Typeᵉ</a> <a id="4158" href="structured-types.wild-monoids%25E1%25B5%2589.html#3814" class="Bound">lᵉ</a>
  <a id="4163" href="structured-types.wild-monoids%25E1%25B5%2589.html#4116" class="Function">pointed-type-Wild-Monoidᵉ</a> <a id="4189" class="Symbol">=</a>
    <a id="4195" href="structured-types.h-spaces%25E1%25B5%2589.html#2897" class="Function">pointed-type-H-Spaceᵉ</a> <a id="4217" href="structured-types.wild-monoids%25E1%25B5%2589.html#3860" class="Function">h-space-Wild-Monoidᵉ</a>

  <a id="4241" href="structured-types.wild-monoids%25E1%25B5%2589.html#4241" class="Function">coherent-unital-mul-Wild-Monoidᵉ</a> <a id="4274" class="Symbol">:</a>
    <a id="4280" href="structured-types.h-spaces%25E1%25B5%2589.html#1701" class="Function">coherent-unital-mul-Pointed-Typeᵉ</a> <a id="4314" href="structured-types.wild-monoids%25E1%25B5%2589.html#4116" class="Function">pointed-type-Wild-Monoidᵉ</a>
  <a id="4342" href="structured-types.wild-monoids%25E1%25B5%2589.html#4241" class="Function">coherent-unital-mul-Wild-Monoidᵉ</a> <a id="4375" class="Symbol">=</a>
    <a id="4381" href="structured-types.h-spaces%25E1%25B5%2589.html#3153" class="Function">coherent-unital-mul-H-Spaceᵉ</a> <a id="4410" href="structured-types.wild-monoids%25E1%25B5%2589.html#3860" class="Function">h-space-Wild-Monoidᵉ</a>

  <a id="4434" href="structured-types.wild-monoids%25E1%25B5%2589.html#4434" class="Function">mul-Wild-Monoidᵉ</a> <a id="4451" class="Symbol">:</a> <a id="4453" href="structured-types.wild-monoids%25E1%25B5%2589.html#3931" class="Function">type-Wild-Monoidᵉ</a> <a id="4471" class="Symbol">→</a> <a id="4473" href="structured-types.wild-monoids%25E1%25B5%2589.html#3931" class="Function">type-Wild-Monoidᵉ</a> <a id="4491" class="Symbol">→</a> <a id="4493" href="structured-types.wild-monoids%25E1%25B5%2589.html#3931" class="Function">type-Wild-Monoidᵉ</a>
  <a id="4513" href="structured-types.wild-monoids%25E1%25B5%2589.html#4434" class="Function">mul-Wild-Monoidᵉ</a> <a id="4530" class="Symbol">=</a> <a id="4532" href="structured-types.h-spaces%25E1%25B5%2589.html#3288" class="Function">mul-H-Spaceᵉ</a> <a id="4545" href="structured-types.wild-monoids%25E1%25B5%2589.html#3860" class="Function">h-space-Wild-Monoidᵉ</a>

  <a id="4569" href="structured-types.wild-monoids%25E1%25B5%2589.html#4569" class="Function">mul-Wild-Monoid&#39;ᵉ</a> <a id="4587" class="Symbol">:</a> <a id="4589" href="structured-types.wild-monoids%25E1%25B5%2589.html#3931" class="Function">type-Wild-Monoidᵉ</a> <a id="4607" class="Symbol">→</a> <a id="4609" href="structured-types.wild-monoids%25E1%25B5%2589.html#3931" class="Function">type-Wild-Monoidᵉ</a> <a id="4627" class="Symbol">→</a> <a id="4629" href="structured-types.wild-monoids%25E1%25B5%2589.html#3931" class="Function">type-Wild-Monoidᵉ</a>
  <a id="4649" href="structured-types.wild-monoids%25E1%25B5%2589.html#4569" class="Function">mul-Wild-Monoid&#39;ᵉ</a> <a id="4667" class="Symbol">=</a> <a id="4669" href="structured-types.h-spaces%25E1%25B5%2589.html#3407" class="Function">mul-H-Space&#39;ᵉ</a> <a id="4683" href="structured-types.wild-monoids%25E1%25B5%2589.html#3860" class="Function">h-space-Wild-Monoidᵉ</a>

  <a id="4707" href="structured-types.wild-monoids%25E1%25B5%2589.html#4707" class="Function">ap-mul-Wild-Monoidᵉ</a> <a id="4727" class="Symbol">:</a>
    <a id="4733" class="Symbol">{</a><a id="4734" href="structured-types.wild-monoids%25E1%25B5%2589.html#4734" class="Bound">aᵉ</a> <a id="4737" href="structured-types.wild-monoids%25E1%25B5%2589.html#4737" class="Bound">bᵉ</a> <a id="4740" href="structured-types.wild-monoids%25E1%25B5%2589.html#4740" class="Bound">cᵉ</a> <a id="4743" href="structured-types.wild-monoids%25E1%25B5%2589.html#4743" class="Bound">dᵉ</a> <a id="4746" class="Symbol">:</a> <a id="4748" href="structured-types.wild-monoids%25E1%25B5%2589.html#3931" class="Function">type-Wild-Monoidᵉ</a><a id="4765" class="Symbol">}</a> <a id="4767" class="Symbol">→</a>
    <a id="4773" href="structured-types.wild-monoids%25E1%25B5%2589.html#4734" class="Bound">aᵉ</a> <a id="4776" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="4779" href="structured-types.wild-monoids%25E1%25B5%2589.html#4737" class="Bound">bᵉ</a> <a id="4782" class="Symbol">→</a> <a id="4784" href="structured-types.wild-monoids%25E1%25B5%2589.html#4740" class="Bound">cᵉ</a> <a id="4787" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="4790" href="structured-types.wild-monoids%25E1%25B5%2589.html#4743" class="Bound">dᵉ</a> <a id="4793" class="Symbol">→</a> <a id="4795" href="structured-types.wild-monoids%25E1%25B5%2589.html#4434" class="Function">mul-Wild-Monoidᵉ</a> <a id="4812" href="structured-types.wild-monoids%25E1%25B5%2589.html#4734" class="Bound">aᵉ</a> <a id="4815" href="structured-types.wild-monoids%25E1%25B5%2589.html#4740" class="Bound">cᵉ</a> <a id="4818" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="4821" href="structured-types.wild-monoids%25E1%25B5%2589.html#4434" class="Function">mul-Wild-Monoidᵉ</a> <a id="4838" href="structured-types.wild-monoids%25E1%25B5%2589.html#4737" class="Bound">bᵉ</a> <a id="4841" href="structured-types.wild-monoids%25E1%25B5%2589.html#4743" class="Bound">dᵉ</a>
  <a id="4846" href="structured-types.wild-monoids%25E1%25B5%2589.html#4707" class="Function">ap-mul-Wild-Monoidᵉ</a> <a id="4866" class="Symbol">=</a> <a id="4868" href="structured-types.h-spaces%25E1%25B5%2589.html#3519" class="Function">ap-mul-H-Spaceᵉ</a> <a id="4884" href="structured-types.wild-monoids%25E1%25B5%2589.html#3860" class="Function">h-space-Wild-Monoidᵉ</a>

  <a id="4908" href="structured-types.wild-monoids%25E1%25B5%2589.html#4908" class="Function">left-unit-law-mul-Wild-Monoidᵉ</a> <a id="4939" class="Symbol">:</a>
    <a id="4945" class="Symbol">(</a><a id="4946" href="structured-types.wild-monoids%25E1%25B5%2589.html#4946" class="Bound">xᵉ</a> <a id="4949" class="Symbol">:</a> <a id="4951" href="structured-types.wild-monoids%25E1%25B5%2589.html#3931" class="Function">type-Wild-Monoidᵉ</a><a id="4968" class="Symbol">)</a> <a id="4970" class="Symbol">→</a> <a id="4972" href="structured-types.wild-monoids%25E1%25B5%2589.html#4434" class="Function">mul-Wild-Monoidᵉ</a> <a id="4989" href="structured-types.wild-monoids%25E1%25B5%2589.html#4018" class="Function">unit-Wild-Monoidᵉ</a> <a id="5007" href="structured-types.wild-monoids%25E1%25B5%2589.html#4946" class="Bound">xᵉ</a> <a id="5010" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="5013" href="structured-types.wild-monoids%25E1%25B5%2589.html#4946" class="Bound">xᵉ</a>
  <a id="5018" href="structured-types.wild-monoids%25E1%25B5%2589.html#4908" class="Function">left-unit-law-mul-Wild-Monoidᵉ</a> <a id="5049" class="Symbol">=</a>
    <a id="5055" href="structured-types.h-spaces%25E1%25B5%2589.html#3973" class="Function">left-unit-law-mul-H-Spaceᵉ</a> <a id="5082" href="structured-types.wild-monoids%25E1%25B5%2589.html#3860" class="Function">h-space-Wild-Monoidᵉ</a>

  <a id="5106" href="structured-types.wild-monoids%25E1%25B5%2589.html#5106" class="Function">right-unit-law-mul-Wild-Monoidᵉ</a> <a id="5138" class="Symbol">:</a>
    <a id="5144" class="Symbol">(</a><a id="5145" href="structured-types.wild-monoids%25E1%25B5%2589.html#5145" class="Bound">xᵉ</a> <a id="5148" class="Symbol">:</a> <a id="5150" href="structured-types.wild-monoids%25E1%25B5%2589.html#3931" class="Function">type-Wild-Monoidᵉ</a><a id="5167" class="Symbol">)</a> <a id="5169" class="Symbol">→</a> <a id="5171" href="structured-types.wild-monoids%25E1%25B5%2589.html#4434" class="Function">mul-Wild-Monoidᵉ</a> <a id="5188" href="structured-types.wild-monoids%25E1%25B5%2589.html#5145" class="Bound">xᵉ</a> <a id="5191" href="structured-types.wild-monoids%25E1%25B5%2589.html#4018" class="Function">unit-Wild-Monoidᵉ</a> <a id="5209" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="5212" href="structured-types.wild-monoids%25E1%25B5%2589.html#5145" class="Bound">xᵉ</a>
  <a id="5217" href="structured-types.wild-monoids%25E1%25B5%2589.html#5106" class="Function">right-unit-law-mul-Wild-Monoidᵉ</a> <a id="5249" class="Symbol">=</a>
    <a id="5255" href="structured-types.h-spaces%25E1%25B5%2589.html#4147" class="Function">right-unit-law-mul-H-Spaceᵉ</a> <a id="5283" href="structured-types.wild-monoids%25E1%25B5%2589.html#3860" class="Function">h-space-Wild-Monoidᵉ</a>

  <a id="5307" href="structured-types.wild-monoids%25E1%25B5%2589.html#5307" class="Function">coh-unit-laws-mul-Wild-Monoidᵉ</a> <a id="5338" class="Symbol">:</a>
    <a id="5344" class="Symbol">(</a> <a id="5346" href="structured-types.wild-monoids%25E1%25B5%2589.html#4908" class="Function">left-unit-law-mul-Wild-Monoidᵉ</a> <a id="5377" href="structured-types.wild-monoids%25E1%25B5%2589.html#4018" class="Function">unit-Wild-Monoidᵉ</a><a id="5394" class="Symbol">)</a> <a id="5396" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a>
    <a id="5403" class="Symbol">(</a> <a id="5405" href="structured-types.wild-monoids%25E1%25B5%2589.html#5106" class="Function">right-unit-law-mul-Wild-Monoidᵉ</a> <a id="5437" href="structured-types.wild-monoids%25E1%25B5%2589.html#4018" class="Function">unit-Wild-Monoidᵉ</a><a id="5454" class="Symbol">)</a>
  <a id="5458" href="structured-types.wild-monoids%25E1%25B5%2589.html#5307" class="Function">coh-unit-laws-mul-Wild-Monoidᵉ</a> <a id="5489" class="Symbol">=</a>
    <a id="5495" href="structured-types.h-spaces%25E1%25B5%2589.html#4330" class="Function">coh-unit-laws-mul-H-Spaceᵉ</a> <a id="5522" href="structured-types.wild-monoids%25E1%25B5%2589.html#3860" class="Function">h-space-Wild-Monoidᵉ</a>

  <a id="5546" href="structured-types.wild-monoids%25E1%25B5%2589.html#5546" class="Function">unital-associator-Wild-Monoidᵉ</a> <a id="5577" class="Symbol">:</a>
    <a id="5583" href="structured-types.wild-monoids%25E1%25B5%2589.html#3570" class="Function">unital-associatorᵉ</a> <a id="5602" href="structured-types.wild-monoids%25E1%25B5%2589.html#3860" class="Function">h-space-Wild-Monoidᵉ</a>
  <a id="5625" href="structured-types.wild-monoids%25E1%25B5%2589.html#5546" class="Function">unital-associator-Wild-Monoidᵉ</a> <a id="5656" class="Symbol">=</a> <a id="5658" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="5663" href="structured-types.wild-monoids%25E1%25B5%2589.html#3827" class="Bound">Mᵉ</a>

  <a id="5669" href="structured-types.wild-monoids%25E1%25B5%2589.html#5669" class="Function">associator-Wild-Monoidᵉ</a> <a id="5693" class="Symbol">:</a>
    <a id="5699" href="structured-types.wild-monoids%25E1%25B5%2589.html#2210" class="Function">associator-H-Spaceᵉ</a> <a id="5719" href="structured-types.wild-monoids%25E1%25B5%2589.html#3860" class="Function">h-space-Wild-Monoidᵉ</a>
  <a id="5742" href="structured-types.wild-monoids%25E1%25B5%2589.html#5669" class="Function">associator-Wild-Monoidᵉ</a> <a id="5766" class="Symbol">=</a> <a id="5768" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="5773" href="structured-types.wild-monoids%25E1%25B5%2589.html#5546" class="Function">unital-associator-Wild-Monoidᵉ</a>

  <a id="5807" href="structured-types.wild-monoids%25E1%25B5%2589.html#5807" class="Function">associative-mul-Wild-Monoidᵉ</a> <a id="5836" class="Symbol">:</a>
    <a id="5842" class="Symbol">(</a><a id="5843" href="structured-types.wild-monoids%25E1%25B5%2589.html#5843" class="Bound">xᵉ</a> <a id="5846" href="structured-types.wild-monoids%25E1%25B5%2589.html#5846" class="Bound">yᵉ</a> <a id="5849" href="structured-types.wild-monoids%25E1%25B5%2589.html#5849" class="Bound">zᵉ</a> <a id="5852" class="Symbol">:</a> <a id="5854" href="structured-types.wild-monoids%25E1%25B5%2589.html#3931" class="Function">type-Wild-Monoidᵉ</a><a id="5871" class="Symbol">)</a> <a id="5873" class="Symbol">→</a>
    <a id="5879" class="Symbol">(</a> <a id="5881" href="structured-types.wild-monoids%25E1%25B5%2589.html#4434" class="Function">mul-Wild-Monoidᵉ</a> <a id="5898" class="Symbol">(</a><a id="5899" href="structured-types.wild-monoids%25E1%25B5%2589.html#4434" class="Function">mul-Wild-Monoidᵉ</a> <a id="5916" href="structured-types.wild-monoids%25E1%25B5%2589.html#5843" class="Bound">xᵉ</a> <a id="5919" href="structured-types.wild-monoids%25E1%25B5%2589.html#5846" class="Bound">yᵉ</a><a id="5921" class="Symbol">)</a> <a id="5923" href="structured-types.wild-monoids%25E1%25B5%2589.html#5849" class="Bound">zᵉ</a><a id="5925" class="Symbol">)</a> <a id="5927" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a>
    <a id="5934" class="Symbol">(</a> <a id="5936" href="structured-types.wild-monoids%25E1%25B5%2589.html#4434" class="Function">mul-Wild-Monoidᵉ</a> <a id="5953" href="structured-types.wild-monoids%25E1%25B5%2589.html#5843" class="Bound">xᵉ</a> <a id="5956" class="Symbol">(</a><a id="5957" href="structured-types.wild-monoids%25E1%25B5%2589.html#4434" class="Function">mul-Wild-Monoidᵉ</a> <a id="5974" href="structured-types.wild-monoids%25E1%25B5%2589.html#5846" class="Bound">yᵉ</a> <a id="5977" href="structured-types.wild-monoids%25E1%25B5%2589.html#5849" class="Bound">zᵉ</a><a id="5979" class="Symbol">))</a>
  <a id="5984" href="structured-types.wild-monoids%25E1%25B5%2589.html#5807" class="Function">associative-mul-Wild-Monoidᵉ</a> <a id="6013" class="Symbol">=</a> <a id="6015" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="6020" href="structured-types.wild-monoids%25E1%25B5%2589.html#5546" class="Function">unital-associator-Wild-Monoidᵉ</a>

  <a id="6054" href="structured-types.wild-monoids%25E1%25B5%2589.html#6054" class="Function">unit-law-110-associative-Wild-Monoidᵉ</a> <a id="6092" class="Symbol">:</a>
    <a id="6098" class="Symbol">(</a><a id="6099" href="structured-types.wild-monoids%25E1%25B5%2589.html#6099" class="Bound">xᵉ</a> <a id="6102" href="structured-types.wild-monoids%25E1%25B5%2589.html#6102" class="Bound">yᵉ</a> <a id="6105" class="Symbol">:</a> <a id="6107" href="structured-types.wild-monoids%25E1%25B5%2589.html#3931" class="Function">type-Wild-Monoidᵉ</a><a id="6124" class="Symbol">)</a> <a id="6126" class="Symbol">→</a>
    <a id="6132" href="foundation-core.identity-types%25E1%25B5%2589.html#2647" class="Datatype">Idᵉ</a>
      <a id="6142" class="Symbol">(</a> <a id="6144" class="Symbol">(</a> <a id="6146" href="structured-types.wild-monoids%25E1%25B5%2589.html#5807" class="Function">associative-mul-Wild-Monoidᵉ</a> <a id="6175" href="structured-types.wild-monoids%25E1%25B5%2589.html#6099" class="Bound">xᵉ</a> <a id="6178" href="structured-types.wild-monoids%25E1%25B5%2589.html#6102" class="Bound">yᵉ</a> <a id="6181" href="structured-types.wild-monoids%25E1%25B5%2589.html#4018" class="Function">unit-Wild-Monoidᵉ</a><a id="6198" class="Symbol">)</a> <a id="6200" href="foundation-core.identity-types%25E1%25B5%2589.html#5906" class="Function Operator">∙ᵉ</a>
        <a id="6211" class="Symbol">(</a> <a id="6213" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html#735" class="Function">apᵉ</a> <a id="6217" class="Symbol">(</a><a id="6218" href="structured-types.wild-monoids%25E1%25B5%2589.html#4434" class="Function">mul-Wild-Monoidᵉ</a> <a id="6235" href="structured-types.wild-monoids%25E1%25B5%2589.html#6099" class="Bound">xᵉ</a><a id="6237" class="Symbol">)</a> <a id="6239" class="Symbol">(</a><a id="6240" href="structured-types.wild-monoids%25E1%25B5%2589.html#5106" class="Function">right-unit-law-mul-Wild-Monoidᵉ</a> <a id="6272" href="structured-types.wild-monoids%25E1%25B5%2589.html#6102" class="Bound">yᵉ</a><a id="6274" class="Symbol">)))</a>
      <a id="6284" class="Symbol">(</a> <a id="6286" href="structured-types.wild-monoids%25E1%25B5%2589.html#5106" class="Function">right-unit-law-mul-Wild-Monoidᵉ</a> <a id="6318" class="Symbol">(</a><a id="6319" href="structured-types.wild-monoids%25E1%25B5%2589.html#4434" class="Function">mul-Wild-Monoidᵉ</a> <a id="6336" href="structured-types.wild-monoids%25E1%25B5%2589.html#6099" class="Bound">xᵉ</a> <a id="6339" href="structured-types.wild-monoids%25E1%25B5%2589.html#6102" class="Bound">yᵉ</a><a id="6341" class="Symbol">))</a>
  <a id="6346" href="structured-types.wild-monoids%25E1%25B5%2589.html#6054" class="Function">unit-law-110-associative-Wild-Monoidᵉ</a> <a id="6384" class="Symbol">=</a> <a id="6386" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="6391" class="Symbol">(</a><a id="6392" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="6397" class="Symbol">(</a><a id="6398" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="6403" class="Symbol">(</a><a id="6404" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="6409" class="Symbol">(</a><a id="6410" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="6415" href="structured-types.wild-monoids%25E1%25B5%2589.html#3827" class="Bound">Mᵉ</a><a id="6417" class="Symbol">))))</a>
</pre>