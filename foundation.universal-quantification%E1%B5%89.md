# Universal quantification

<pre class="Agda"><a id="37" class="Keyword">module</a> <a id="44" href="foundation.universal-quantification%25E1%25B5%2589.html" class="Module">foundation.universal-quantificationᵉ</a> <a id="81" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="137" class="Keyword">open</a> <a id="142" class="Keyword">import</a> <a id="149" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="182" class="Keyword">open</a> <a id="187" class="Keyword">import</a> <a id="194" href="foundation.evaluation-functions%25E1%25B5%2589.html" class="Module">foundation.evaluation-functionsᵉ</a>
<a id="227" class="Keyword">open</a> <a id="232" class="Keyword">import</a> <a id="239" href="foundation.logical-equivalences%25E1%25B5%2589.html" class="Module">foundation.logical-equivalencesᵉ</a>
<a id="272" class="Keyword">open</a> <a id="277" class="Keyword">import</a> <a id="284" href="foundation.propositional-truncations%25E1%25B5%2589.html" class="Module">foundation.propositional-truncationsᵉ</a>
<a id="322" class="Keyword">open</a> <a id="327" class="Keyword">import</a> <a id="334" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="363" class="Keyword">open</a> <a id="368" class="Keyword">import</a> <a id="375" href="foundation-core.equivalences%25E1%25B5%2589.html" class="Module">foundation-core.equivalencesᵉ</a>
<a id="405" class="Keyword">open</a> <a id="410" class="Keyword">import</a> <a id="417" href="foundation-core.function-types%25E1%25B5%2589.html" class="Module">foundation-core.function-typesᵉ</a>
<a id="449" class="Keyword">open</a> <a id="454" class="Keyword">import</a> <a id="461" href="foundation-core.propositions%25E1%25B5%2589.html" class="Module">foundation-core.propositionsᵉ</a>
</pre>
</details>

## Idea

Given a type `A` and a [subtype](foundation-core.subtypes.md) `P : A → Prop`,
the
{{#concept "universal quantification" Disambiguation="on a subtype" WDID=Q126695 WD="universal quantification"}}

```text
  ∀ (x : A), (P x)
```

is the [proposition](foundation-core.propositions.md) that there exists a proof
of `P x` for every `x` in `A`.

The
{{#concept "universal property" Disambiguation="of universal quantification" Agda=universal-property-for-all}}
of universal quantification states that it is the
[greatest lower bound](order-theory.greatest-lower-bounds-large-posets.md) on
the family of propositions `P` in the
[locale of propositions](foundation.large-locale-of-propositions.md), by which
we mean that for every proposition `Q` we have the
[logical equivalence](foundation.logical-equivalences.md)

```text
  (∀ (a : A), (R → P a)) ↔ (R → ∀ (a : A), (P a))
```

**Notation.** Because of syntactic limitations of the Agda language, we cannot
use `∀` for the universal quantification in formalizations, and instead use
`∀'`.

## Definitions

### Universal quantification

<pre class="Agda"><a id="1606" class="Keyword">module</a> <a id="1613" href="foundation.universal-quantification%25E1%25B5%2589.html#1613" class="Module">_</a>
  <a id="1617" class="Symbol">{</a><a id="1618" href="foundation.universal-quantification%25E1%25B5%2589.html#1618" class="Bound">l1ᵉ</a> <a id="1622" href="foundation.universal-quantification%25E1%25B5%2589.html#1622" class="Bound">l2ᵉ</a> <a id="1626" class="Symbol">:</a> <a id="1628" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1633" class="Symbol">}</a> <a id="1635" class="Symbol">(</a><a id="1636" href="foundation.universal-quantification%25E1%25B5%2589.html#1636" class="Bound">Aᵉ</a> <a id="1639" class="Symbol">:</a> <a id="1641" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1645" href="foundation.universal-quantification%25E1%25B5%2589.html#1618" class="Bound">l1ᵉ</a><a id="1648" class="Symbol">)</a> <a id="1650" class="Symbol">(</a><a id="1651" href="foundation.universal-quantification%25E1%25B5%2589.html#1651" class="Bound">Pᵉ</a> <a id="1654" class="Symbol">:</a> <a id="1656" href="foundation.universal-quantification%25E1%25B5%2589.html#1636" class="Bound">Aᵉ</a> <a id="1659" class="Symbol">→</a> <a id="1661" href="foundation-core.propositions%25E1%25B5%2589.html#1181" class="Function">Propᵉ</a> <a id="1667" href="foundation.universal-quantification%25E1%25B5%2589.html#1622" class="Bound">l2ᵉ</a><a id="1670" class="Symbol">)</a>
  <a id="1674" class="Keyword">where</a>

  <a id="1683" href="foundation.universal-quantification%25E1%25B5%2589.html#1683" class="Function">for-all-Propᵉ</a> <a id="1697" class="Symbol">:</a> <a id="1699" href="foundation-core.propositions%25E1%25B5%2589.html#1181" class="Function">Propᵉ</a> <a id="1705" class="Symbol">(</a><a id="1706" href="foundation.universal-quantification%25E1%25B5%2589.html#1618" class="Bound">l1ᵉ</a> <a id="1710" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1712" href="foundation.universal-quantification%25E1%25B5%2589.html#1622" class="Bound">l2ᵉ</a><a id="1715" class="Symbol">)</a>
  <a id="1719" href="foundation.universal-quantification%25E1%25B5%2589.html#1683" class="Function">for-all-Propᵉ</a> <a id="1733" class="Symbol">=</a> <a id="1735" href="foundation-core.propositions%25E1%25B5%2589.html#6460" class="Function">Π-Propᵉ</a> <a id="1743" href="foundation.universal-quantification%25E1%25B5%2589.html#1636" class="Bound">Aᵉ</a> <a id="1746" href="foundation.universal-quantification%25E1%25B5%2589.html#1651" class="Bound">Pᵉ</a>

  <a id="1752" href="foundation.universal-quantification%25E1%25B5%2589.html#1752" class="Function">type-for-all-Propᵉ</a> <a id="1771" class="Symbol">:</a> <a id="1773" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1777" class="Symbol">(</a><a id="1778" href="foundation.universal-quantification%25E1%25B5%2589.html#1618" class="Bound">l1ᵉ</a> <a id="1782" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1784" href="foundation.universal-quantification%25E1%25B5%2589.html#1622" class="Bound">l2ᵉ</a><a id="1787" class="Symbol">)</a>
  <a id="1791" href="foundation.universal-quantification%25E1%25B5%2589.html#1752" class="Function">type-for-all-Propᵉ</a> <a id="1810" class="Symbol">=</a> <a id="1812" href="foundation-core.propositions%25E1%25B5%2589.html#1288" class="Function">type-Propᵉ</a> <a id="1823" href="foundation.universal-quantification%25E1%25B5%2589.html#1683" class="Function">for-all-Propᵉ</a>

  <a id="1840" href="foundation.universal-quantification%25E1%25B5%2589.html#1840" class="Function">is-prop-for-all-Propᵉ</a> <a id="1862" class="Symbol">:</a> <a id="1864" href="foundation-core.propositions%25E1%25B5%2589.html#1041" class="Function">is-propᵉ</a> <a id="1873" href="foundation.universal-quantification%25E1%25B5%2589.html#1752" class="Function">type-for-all-Propᵉ</a>
  <a id="1894" href="foundation.universal-quantification%25E1%25B5%2589.html#1840" class="Function">is-prop-for-all-Propᵉ</a> <a id="1916" class="Symbol">=</a> <a id="1918" href="foundation-core.propositions%25E1%25B5%2589.html#1361" class="Function">is-prop-type-Propᵉ</a> <a id="1937" href="foundation.universal-quantification%25E1%25B5%2589.html#1683" class="Function">for-all-Propᵉ</a>

  <a id="1954" href="foundation.universal-quantification%25E1%25B5%2589.html#1954" class="Function">for-allᵉ</a> <a id="1963" class="Symbol">:</a> <a id="1965" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1969" class="Symbol">(</a><a id="1970" href="foundation.universal-quantification%25E1%25B5%2589.html#1618" class="Bound">l1ᵉ</a> <a id="1974" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1976" href="foundation.universal-quantification%25E1%25B5%2589.html#1622" class="Bound">l2ᵉ</a><a id="1979" class="Symbol">)</a>
  <a id="1983" href="foundation.universal-quantification%25E1%25B5%2589.html#1954" class="Function">for-allᵉ</a> <a id="1992" class="Symbol">=</a> <a id="1994" href="foundation.universal-quantification%25E1%25B5%2589.html#1752" class="Function">type-for-all-Propᵉ</a>

  <a id="2016" href="foundation.universal-quantification%25E1%25B5%2589.html#2016" class="Function">∀&#39;ᵉ</a> <a id="2020" class="Symbol">:</a> <a id="2022" href="foundation-core.propositions%25E1%25B5%2589.html#1181" class="Function">Propᵉ</a> <a id="2028" class="Symbol">(</a><a id="2029" href="foundation.universal-quantification%25E1%25B5%2589.html#1618" class="Bound">l1ᵉ</a> <a id="2033" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2035" href="foundation.universal-quantification%25E1%25B5%2589.html#1622" class="Bound">l2ᵉ</a><a id="2038" class="Symbol">)</a>
  <a id="2042" href="foundation.universal-quantification%25E1%25B5%2589.html#2016" class="Function">∀&#39;ᵉ</a> <a id="2046" class="Symbol">=</a> <a id="2048" href="foundation.universal-quantification%25E1%25B5%2589.html#1683" class="Function">for-all-Propᵉ</a>
</pre>
### The universal property of universal quantification

The
{{#concept "universal property" Disambiguation="of universal quantification" Agda=universal-property-for-all}}
of the universal quantification `∀ (a : A), (P a)` states that for every
proposition `R`, the canonical map

```text
  (∀ (a : A), (R → P a)) → (R → ∀ (a : A), (P a))
```

is a [logical equivalence](foundation.logical-equivalences.md). Indeed, this
holds for any type `R`.

<pre class="Agda"><a id="2520" class="Keyword">module</a> <a id="2527" href="foundation.universal-quantification%25E1%25B5%2589.html#2527" class="Module">_</a>
  <a id="2531" class="Symbol">{</a><a id="2532" href="foundation.universal-quantification%25E1%25B5%2589.html#2532" class="Bound">l1ᵉ</a> <a id="2536" href="foundation.universal-quantification%25E1%25B5%2589.html#2536" class="Bound">l2ᵉ</a> <a id="2540" class="Symbol">:</a> <a id="2542" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2547" class="Symbol">}</a> <a id="2549" class="Symbol">(</a><a id="2550" href="foundation.universal-quantification%25E1%25B5%2589.html#2550" class="Bound">Aᵉ</a> <a id="2553" class="Symbol">:</a> <a id="2555" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2559" href="foundation.universal-quantification%25E1%25B5%2589.html#2532" class="Bound">l1ᵉ</a><a id="2562" class="Symbol">)</a> <a id="2564" class="Symbol">(</a><a id="2565" href="foundation.universal-quantification%25E1%25B5%2589.html#2565" class="Bound">Pᵉ</a> <a id="2568" class="Symbol">:</a> <a id="2570" href="foundation.universal-quantification%25E1%25B5%2589.html#2550" class="Bound">Aᵉ</a> <a id="2573" class="Symbol">→</a> <a id="2575" href="foundation-core.propositions%25E1%25B5%2589.html#1181" class="Function">Propᵉ</a> <a id="2581" href="foundation.universal-quantification%25E1%25B5%2589.html#2536" class="Bound">l2ᵉ</a><a id="2584" class="Symbol">)</a>
  <a id="2588" class="Keyword">where</a>

  <a id="2597" href="foundation.universal-quantification%25E1%25B5%2589.html#2597" class="Function">universal-property-for-allᵉ</a> <a id="2625" class="Symbol">:</a> <a id="2627" class="Symbol">{</a><a id="2628" href="foundation.universal-quantification%25E1%25B5%2589.html#2628" class="Bound">l3ᵉ</a> <a id="2632" class="Symbol">:</a> <a id="2634" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2639" class="Symbol">}</a> <a id="2641" class="Symbol">(</a><a id="2642" href="foundation.universal-quantification%25E1%25B5%2589.html#2642" class="Bound">Sᵉ</a> <a id="2645" class="Symbol">:</a> <a id="2647" href="foundation-core.propositions%25E1%25B5%2589.html#1181" class="Function">Propᵉ</a> <a id="2653" href="foundation.universal-quantification%25E1%25B5%2589.html#2628" class="Bound">l3ᵉ</a><a id="2656" class="Symbol">)</a> <a id="2658" class="Symbol">→</a> <a id="2660" href="Agda.Primitive.html#553" class="Primitive">UUωᵉ</a>
  <a id="2667" href="foundation.universal-quantification%25E1%25B5%2589.html#2597" class="Function">universal-property-for-allᵉ</a> <a id="2695" href="foundation.universal-quantification%25E1%25B5%2589.html#2695" class="Bound">Sᵉ</a> <a id="2698" class="Symbol">=</a>
    <a id="2704" class="Symbol">{</a><a id="2705" href="foundation.universal-quantification%25E1%25B5%2589.html#2705" class="Bound">lᵉ</a> <a id="2708" class="Symbol">:</a> <a id="2710" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2715" class="Symbol">}</a> <a id="2717" class="Symbol">(</a><a id="2718" href="foundation.universal-quantification%25E1%25B5%2589.html#2718" class="Bound">Rᵉ</a> <a id="2721" class="Symbol">:</a> <a id="2723" href="foundation-core.propositions%25E1%25B5%2589.html#1181" class="Function">Propᵉ</a> <a id="2729" href="foundation.universal-quantification%25E1%25B5%2589.html#2705" class="Bound">lᵉ</a><a id="2731" class="Symbol">)</a> <a id="2733" class="Symbol">→</a>
    <a id="2739" href="foundation-core.propositions%25E1%25B5%2589.html#1288" class="Function">type-Propᵉ</a> <a id="2750" class="Symbol">((</a><a id="2752" href="foundation.universal-quantification%25E1%25B5%2589.html#2016" class="Function">∀&#39;ᵉ</a> <a id="2756" href="foundation.universal-quantification%25E1%25B5%2589.html#2550" class="Bound">Aᵉ</a> <a id="2759" class="Symbol">(λ</a> <a id="2762" href="foundation.universal-quantification%25E1%25B5%2589.html#2762" class="Bound">aᵉ</a> <a id="2765" class="Symbol">→</a> <a id="2767" href="foundation.universal-quantification%25E1%25B5%2589.html#2718" class="Bound">Rᵉ</a> <a id="2770" href="foundation-core.propositions%25E1%25B5%2589.html#8679" class="Function Operator">⇒ᵉ</a> <a id="2773" href="foundation.universal-quantification%25E1%25B5%2589.html#2565" class="Bound">Pᵉ</a> <a id="2776" href="foundation.universal-quantification%25E1%25B5%2589.html#2762" class="Bound">aᵉ</a><a id="2778" class="Symbol">))</a> <a id="2781" href="foundation.logical-equivalences%25E1%25B5%2589.html#3027" class="Function Operator">⇔ᵉ</a> <a id="2784" class="Symbol">(</a><a id="2785" href="foundation.universal-quantification%25E1%25B5%2589.html#2718" class="Bound">Rᵉ</a> <a id="2788" href="foundation-core.propositions%25E1%25B5%2589.html#8679" class="Function Operator">⇒ᵉ</a> <a id="2791" href="foundation.universal-quantification%25E1%25B5%2589.html#2695" class="Bound">Sᵉ</a><a id="2793" class="Symbol">))</a>

  <a id="2799" href="foundation.universal-quantification%25E1%25B5%2589.html#2799" class="Function">ev-for-allᵉ</a> <a id="2811" class="Symbol">:</a>
    <a id="2817" class="Symbol">{</a><a id="2818" href="foundation.universal-quantification%25E1%25B5%2589.html#2818" class="Bound">lᵉ</a> <a id="2821" class="Symbol">:</a> <a id="2823" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2828" class="Symbol">}</a> <a id="2830" class="Symbol">{</a><a id="2831" href="foundation.universal-quantification%25E1%25B5%2589.html#2831" class="Bound">Bᵉ</a> <a id="2834" class="Symbol">:</a> <a id="2836" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2840" href="foundation.universal-quantification%25E1%25B5%2589.html#2818" class="Bound">lᵉ</a><a id="2842" class="Symbol">}</a> <a id="2844" class="Symbol">→</a>
    <a id="2850" href="foundation.universal-quantification%25E1%25B5%2589.html#1954" class="Function">for-allᵉ</a> <a id="2859" href="foundation.universal-quantification%25E1%25B5%2589.html#2550" class="Bound">Aᵉ</a> <a id="2862" class="Symbol">(λ</a> <a id="2865" href="foundation.universal-quantification%25E1%25B5%2589.html#2865" class="Bound">aᵉ</a> <a id="2868" class="Symbol">→</a> <a id="2870" href="foundation-core.propositions%25E1%25B5%2589.html#7998" class="Function">function-Propᵉ</a> <a id="2885" href="foundation.universal-quantification%25E1%25B5%2589.html#2831" class="Bound">Bᵉ</a> <a id="2888" class="Symbol">(</a><a id="2889" href="foundation.universal-quantification%25E1%25B5%2589.html#2565" class="Bound">Pᵉ</a> <a id="2892" href="foundation.universal-quantification%25E1%25B5%2589.html#2865" class="Bound">aᵉ</a><a id="2894" class="Symbol">))</a> <a id="2897" class="Symbol">→</a> <a id="2899" href="foundation.universal-quantification%25E1%25B5%2589.html#2831" class="Bound">Bᵉ</a> <a id="2902" class="Symbol">→</a> <a id="2904" href="foundation.universal-quantification%25E1%25B5%2589.html#1954" class="Function">for-allᵉ</a> <a id="2913" href="foundation.universal-quantification%25E1%25B5%2589.html#2550" class="Bound">Aᵉ</a> <a id="2916" href="foundation.universal-quantification%25E1%25B5%2589.html#2565" class="Bound">Pᵉ</a>
  <a id="2921" href="foundation.universal-quantification%25E1%25B5%2589.html#2799" class="Function">ev-for-allᵉ</a> <a id="2933" href="foundation.universal-quantification%25E1%25B5%2589.html#2933" class="Bound">fᵉ</a> <a id="2936" href="foundation.universal-quantification%25E1%25B5%2589.html#2936" class="Bound">rᵉ</a> <a id="2939" href="foundation.universal-quantification%25E1%25B5%2589.html#2939" class="Bound">aᵉ</a> <a id="2942" class="Symbol">=</a> <a id="2944" href="foundation.universal-quantification%25E1%25B5%2589.html#2933" class="Bound">fᵉ</a> <a id="2947" href="foundation.universal-quantification%25E1%25B5%2589.html#2939" class="Bound">aᵉ</a> <a id="2950" href="foundation.universal-quantification%25E1%25B5%2589.html#2936" class="Bound">rᵉ</a>
</pre>
## Properties

### Universal quantification satisfies its universal property

<pre class="Agda"><a id="3044" class="Keyword">module</a> <a id="3051" href="foundation.universal-quantification%25E1%25B5%2589.html#3051" class="Module">_</a>
  <a id="3055" class="Symbol">{</a><a id="3056" href="foundation.universal-quantification%25E1%25B5%2589.html#3056" class="Bound">l1ᵉ</a> <a id="3060" href="foundation.universal-quantification%25E1%25B5%2589.html#3060" class="Bound">l2ᵉ</a> <a id="3064" class="Symbol">:</a> <a id="3066" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3071" class="Symbol">}</a> <a id="3073" class="Symbol">(</a><a id="3074" href="foundation.universal-quantification%25E1%25B5%2589.html#3074" class="Bound">Aᵉ</a> <a id="3077" class="Symbol">:</a> <a id="3079" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="3083" href="foundation.universal-quantification%25E1%25B5%2589.html#3056" class="Bound">l1ᵉ</a><a id="3086" class="Symbol">)</a> <a id="3088" class="Symbol">(</a><a id="3089" href="foundation.universal-quantification%25E1%25B5%2589.html#3089" class="Bound">Pᵉ</a> <a id="3092" class="Symbol">:</a> <a id="3094" href="foundation.universal-quantification%25E1%25B5%2589.html#3074" class="Bound">Aᵉ</a> <a id="3097" class="Symbol">→</a> <a id="3099" href="foundation-core.propositions%25E1%25B5%2589.html#1181" class="Function">Propᵉ</a> <a id="3105" href="foundation.universal-quantification%25E1%25B5%2589.html#3060" class="Bound">l2ᵉ</a><a id="3108" class="Symbol">)</a>
  <a id="3112" class="Keyword">where</a>

  <a id="3121" href="foundation.universal-quantification%25E1%25B5%2589.html#3121" class="Function">map-up-for-allᵉ</a> <a id="3137" class="Symbol">:</a>
    <a id="3143" class="Symbol">{</a><a id="3144" href="foundation.universal-quantification%25E1%25B5%2589.html#3144" class="Bound">lᵉ</a> <a id="3147" class="Symbol">:</a> <a id="3149" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3154" class="Symbol">}</a> <a id="3156" class="Symbol">{</a><a id="3157" href="foundation.universal-quantification%25E1%25B5%2589.html#3157" class="Bound">Bᵉ</a> <a id="3160" class="Symbol">:</a> <a id="3162" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="3166" href="foundation.universal-quantification%25E1%25B5%2589.html#3144" class="Bound">lᵉ</a><a id="3168" class="Symbol">}</a> <a id="3170" class="Symbol">→</a>
    <a id="3176" class="Symbol">(</a><a id="3177" href="foundation.universal-quantification%25E1%25B5%2589.html#3157" class="Bound">Bᵉ</a> <a id="3180" class="Symbol">→</a> <a id="3182" href="foundation.universal-quantification%25E1%25B5%2589.html#1954" class="Function">for-allᵉ</a> <a id="3191" href="foundation.universal-quantification%25E1%25B5%2589.html#3074" class="Bound">Aᵉ</a> <a id="3194" href="foundation.universal-quantification%25E1%25B5%2589.html#3089" class="Bound">Pᵉ</a><a id="3196" class="Symbol">)</a> <a id="3198" class="Symbol">→</a> <a id="3200" href="foundation.universal-quantification%25E1%25B5%2589.html#1954" class="Function">for-allᵉ</a> <a id="3209" href="foundation.universal-quantification%25E1%25B5%2589.html#3074" class="Bound">Aᵉ</a> <a id="3212" class="Symbol">(λ</a> <a id="3215" href="foundation.universal-quantification%25E1%25B5%2589.html#3215" class="Bound">aᵉ</a> <a id="3218" class="Symbol">→</a> <a id="3220" href="foundation-core.propositions%25E1%25B5%2589.html#7998" class="Function">function-Propᵉ</a> <a id="3235" href="foundation.universal-quantification%25E1%25B5%2589.html#3157" class="Bound">Bᵉ</a> <a id="3238" class="Symbol">(</a><a id="3239" href="foundation.universal-quantification%25E1%25B5%2589.html#3089" class="Bound">Pᵉ</a> <a id="3242" href="foundation.universal-quantification%25E1%25B5%2589.html#3215" class="Bound">aᵉ</a><a id="3244" class="Symbol">))</a>
  <a id="3249" href="foundation.universal-quantification%25E1%25B5%2589.html#3121" class="Function">map-up-for-allᵉ</a> <a id="3265" href="foundation.universal-quantification%25E1%25B5%2589.html#3265" class="Bound">fᵉ</a> <a id="3268" href="foundation.universal-quantification%25E1%25B5%2589.html#3268" class="Bound">aᵉ</a> <a id="3271" href="foundation.universal-quantification%25E1%25B5%2589.html#3271" class="Bound">rᵉ</a> <a id="3274" class="Symbol">=</a> <a id="3276" href="foundation.universal-quantification%25E1%25B5%2589.html#3265" class="Bound">fᵉ</a> <a id="3279" href="foundation.universal-quantification%25E1%25B5%2589.html#3271" class="Bound">rᵉ</a> <a id="3282" href="foundation.universal-quantification%25E1%25B5%2589.html#3268" class="Bound">aᵉ</a>

  <a id="3288" href="foundation.universal-quantification%25E1%25B5%2589.html#3288" class="Function">is-equiv-ev-for-allᵉ</a> <a id="3309" class="Symbol">:</a>
    <a id="3315" class="Symbol">{</a><a id="3316" href="foundation.universal-quantification%25E1%25B5%2589.html#3316" class="Bound">lᵉ</a> <a id="3319" class="Symbol">:</a> <a id="3321" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3326" class="Symbol">}</a> <a id="3328" class="Symbol">{</a><a id="3329" href="foundation.universal-quantification%25E1%25B5%2589.html#3329" class="Bound">Bᵉ</a> <a id="3332" class="Symbol">:</a> <a id="3334" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="3338" href="foundation.universal-quantification%25E1%25B5%2589.html#3316" class="Bound">lᵉ</a><a id="3340" class="Symbol">}</a> <a id="3342" class="Symbol">→</a> <a id="3344" href="foundation-core.equivalences%25E1%25B5%2589.html#1553" class="Function">is-equivᵉ</a> <a id="3354" class="Symbol">(</a><a id="3355" href="foundation.universal-quantification%25E1%25B5%2589.html#2799" class="Function">ev-for-allᵉ</a> <a id="3367" href="foundation.universal-quantification%25E1%25B5%2589.html#3074" class="Bound">Aᵉ</a> <a id="3370" href="foundation.universal-quantification%25E1%25B5%2589.html#3089" class="Bound">Pᵉ</a> <a id="3373" class="Symbol">{</a><a id="3374" class="Argument">Bᵉ</a> <a id="3377" class="Symbol">=</a> <a id="3379" href="foundation.universal-quantification%25E1%25B5%2589.html#3329" class="Bound">Bᵉ</a><a id="3381" class="Symbol">})</a>
  <a id="3386" href="foundation.universal-quantification%25E1%25B5%2589.html#3288" class="Function">is-equiv-ev-for-allᵉ</a> <a id="3407" class="Symbol">{</a><a id="3408" class="Argument">Bᵉ</a> <a id="3411" class="Symbol">=</a> <a id="3413" href="foundation.universal-quantification%25E1%25B5%2589.html#3413" class="Bound">Bᵉ</a><a id="3415" class="Symbol">}</a> <a id="3417" class="Symbol">=</a>
    <a id="3423" href="foundation.logical-equivalences%25E1%25B5%2589.html#5400" class="Function">is-equiv-has-converseᵉ</a>
      <a id="3452" class="Symbol">(</a> <a id="3454" href="foundation.universal-quantification%25E1%25B5%2589.html#2016" class="Function">∀&#39;ᵉ</a> <a id="3458" href="foundation.universal-quantification%25E1%25B5%2589.html#3074" class="Bound">Aᵉ</a> <a id="3461" class="Symbol">(λ</a> <a id="3464" href="foundation.universal-quantification%25E1%25B5%2589.html#3464" class="Bound">aᵉ</a> <a id="3467" class="Symbol">→</a> <a id="3469" href="foundation-core.propositions%25E1%25B5%2589.html#7998" class="Function">function-Propᵉ</a> <a id="3484" href="foundation.universal-quantification%25E1%25B5%2589.html#3413" class="Bound">Bᵉ</a> <a id="3487" class="Symbol">(</a><a id="3488" href="foundation.universal-quantification%25E1%25B5%2589.html#3089" class="Bound">Pᵉ</a> <a id="3491" href="foundation.universal-quantification%25E1%25B5%2589.html#3464" class="Bound">aᵉ</a><a id="3493" class="Symbol">)))</a>
      <a id="3503" class="Symbol">(</a> <a id="3505" href="foundation-core.propositions%25E1%25B5%2589.html#7998" class="Function">function-Propᵉ</a> <a id="3520" href="foundation.universal-quantification%25E1%25B5%2589.html#3413" class="Bound">Bᵉ</a> <a id="3523" class="Symbol">(</a><a id="3524" href="foundation.universal-quantification%25E1%25B5%2589.html#2016" class="Function">∀&#39;ᵉ</a> <a id="3528" href="foundation.universal-quantification%25E1%25B5%2589.html#3074" class="Bound">Aᵉ</a> <a id="3531" href="foundation.universal-quantification%25E1%25B5%2589.html#3089" class="Bound">Pᵉ</a><a id="3533" class="Symbol">))</a>
      <a id="3542" class="Symbol">(</a> <a id="3544" href="foundation.universal-quantification%25E1%25B5%2589.html#3121" class="Function">map-up-for-allᵉ</a><a id="3559" class="Symbol">)</a>

  <a id="3564" href="foundation.universal-quantification%25E1%25B5%2589.html#3564" class="Function">up-for-allᵉ</a> <a id="3576" class="Symbol">:</a> <a id="3578" href="foundation.universal-quantification%25E1%25B5%2589.html#2597" class="Function">universal-property-for-allᵉ</a> <a id="3606" href="foundation.universal-quantification%25E1%25B5%2589.html#3074" class="Bound">Aᵉ</a> <a id="3609" href="foundation.universal-quantification%25E1%25B5%2589.html#3089" class="Bound">Pᵉ</a> <a id="3612" class="Symbol">(</a><a id="3613" href="foundation.universal-quantification%25E1%25B5%2589.html#2016" class="Function">∀&#39;ᵉ</a> <a id="3617" href="foundation.universal-quantification%25E1%25B5%2589.html#3074" class="Bound">Aᵉ</a> <a id="3620" href="foundation.universal-quantification%25E1%25B5%2589.html#3089" class="Bound">Pᵉ</a><a id="3622" class="Symbol">)</a>
  <a id="3626" href="foundation.universal-quantification%25E1%25B5%2589.html#3564" class="Function">up-for-allᵉ</a> <a id="3638" href="foundation.universal-quantification%25E1%25B5%2589.html#3638" class="Bound">Rᵉ</a> <a id="3641" class="Symbol">=</a> <a id="3643" class="Symbol">(</a><a id="3644" href="foundation.universal-quantification%25E1%25B5%2589.html#2799" class="Function">ev-for-allᵉ</a> <a id="3656" href="foundation.universal-quantification%25E1%25B5%2589.html#3074" class="Bound">Aᵉ</a> <a id="3659" href="foundation.universal-quantification%25E1%25B5%2589.html#3089" class="Bound">Pᵉ</a> <a id="3662" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="3665" href="foundation.universal-quantification%25E1%25B5%2589.html#3121" class="Function">map-up-for-allᵉ</a><a id="3680" class="Symbol">)</a>
</pre>
## See also

- Universal quantification is the indexed counterpart to
  [conjunction](foundation.conjunction.md).

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}

## External links

- [universal quantifier](https://ncatlab.org/nlab/show/universal+quantifier) at
  $n$Lab
- [Universal quantification](https://en.wikipedia.org/wiki/Universal_quantification)
  at Wikipedia