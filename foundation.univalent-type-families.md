# Univalent type families

<pre class="Agda"><a id="36" class="Keyword">module</a> <a id="43" href="foundation.univalent-type-families.html" class="Module">foundation.univalent-type-families</a> <a id="78" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="134" class="Keyword">open</a> <a id="139" class="Keyword">import</a> <a id="146" href="foundation.action-on-identifications-functions.html" class="Module">foundation.action-on-identifications-functions</a>
<a id="193" class="Keyword">open</a> <a id="198" class="Keyword">import</a> <a id="205" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="237" class="Keyword">open</a> <a id="242" class="Keyword">import</a> <a id="249" href="foundation.equality-dependent-pair-types.html" class="Module">foundation.equality-dependent-pair-types</a>
<a id="290" class="Keyword">open</a> <a id="295" class="Keyword">import</a> <a id="302" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="326" class="Keyword">open</a> <a id="331" class="Keyword">import</a> <a id="338" href="foundation.fundamental-theorem-of-identity-types.html" class="Module">foundation.fundamental-theorem-of-identity-types</a>
<a id="387" class="Keyword">open</a> <a id="392" class="Keyword">import</a> <a id="399" href="foundation.identity-systems.html" class="Module">foundation.identity-systems</a>
<a id="427" class="Keyword">open</a> <a id="432" class="Keyword">import</a> <a id="439" href="foundation.iterated-dependent-product-types.html" class="Module">foundation.iterated-dependent-product-types</a>
<a id="483" class="Keyword">open</a> <a id="488" class="Keyword">import</a> <a id="495" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="519" class="Keyword">open</a> <a id="524" class="Keyword">import</a> <a id="531" href="foundation.subuniverses.html" class="Module">foundation.subuniverses</a>
<a id="555" class="Keyword">open</a> <a id="560" class="Keyword">import</a> <a id="567" href="foundation.transport-along-identifications.html" class="Module">foundation.transport-along-identifications</a>
<a id="610" class="Keyword">open</a> <a id="615" class="Keyword">import</a> <a id="622" href="foundation.univalence.html" class="Module">foundation.univalence</a>
<a id="644" class="Keyword">open</a> <a id="649" class="Keyword">import</a> <a id="656" href="foundation.universal-property-identity-systems.html" class="Module">foundation.universal-property-identity-systems</a>
<a id="703" class="Keyword">open</a> <a id="708" class="Keyword">import</a> <a id="715" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="743" class="Keyword">open</a> <a id="748" class="Keyword">import</a> <a id="755" href="foundation-core.embeddings.html" class="Module">foundation-core.embeddings</a>
<a id="782" class="Keyword">open</a> <a id="787" class="Keyword">import</a> <a id="794" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="825" class="Keyword">open</a> <a id="830" class="Keyword">import</a> <a id="837" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="868" class="Keyword">open</a> <a id="873" class="Keyword">import</a> <a id="880" href="foundation-core.sections.html" class="Module">foundation-core.sections</a>
<a id="905" class="Keyword">open</a> <a id="910" class="Keyword">import</a> <a id="917" href="foundation-core.torsorial-type-families.html" class="Module">foundation-core.torsorial-type-families</a>
</pre>
</details>

## Idea

A type family `B` over `A` is said to be
{{#concept "univalent" Disambiguation="type family" Agda=is-univalent}} if the
map

```text
  equiv-tr B : x ＝ y → B x ≃ B y
```

is an [equivalence](foundation-core.equivalences.md) for every `x y : A`. By
[the univalence axiom](foundation-core.univalence.md), this is equivalent to the
type family `B` being an [embedding](foundation-core.embeddings.md) considered
as a map.

## Definition

### The predicate on type families of being univalent

<pre class="Agda"><a id="is-univalent"></a><a id="1480" href="foundation.univalent-type-families.html#1480" class="Function">is-univalent</a> <a id="1493" class="Symbol">:</a>
  <a id="1497" class="Symbol">{</a><a id="1498" href="foundation.univalent-type-families.html#1498" class="Bound">l1</a> <a id="1501" href="foundation.univalent-type-families.html#1501" class="Bound">l2</a> <a id="1504" class="Symbol">:</a> <a id="1506" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1511" class="Symbol">}</a> <a id="1513" class="Symbol">{</a><a id="1514" href="foundation.univalent-type-families.html#1514" class="Bound">A</a> <a id="1516" class="Symbol">:</a> <a id="1518" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1521" href="foundation.univalent-type-families.html#1498" class="Bound">l1</a><a id="1523" class="Symbol">}</a> <a id="1525" class="Symbol">→</a> <a id="1527" class="Symbol">(</a><a id="1528" href="foundation.univalent-type-families.html#1514" class="Bound">A</a> <a id="1530" class="Symbol">→</a> <a id="1532" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1535" href="foundation.univalent-type-families.html#1501" class="Bound">l2</a><a id="1537" class="Symbol">)</a> <a id="1539" class="Symbol">→</a> <a id="1541" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1544" class="Symbol">(</a><a id="1545" href="foundation.univalent-type-families.html#1498" class="Bound">l1</a> <a id="1548" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1550" href="foundation.univalent-type-families.html#1501" class="Bound">l2</a><a id="1552" class="Symbol">)</a>
<a id="1554" href="foundation.univalent-type-families.html#1480" class="Function">is-univalent</a> <a id="1567" class="Symbol">{</a><a id="1568" class="Argument">A</a> <a id="1570" class="Symbol">=</a> <a id="1572" href="foundation.univalent-type-families.html#1572" class="Bound">A</a><a id="1573" class="Symbol">}</a> <a id="1575" href="foundation.univalent-type-families.html#1575" class="Bound">B</a> <a id="1577" class="Symbol">=</a> <a id="1579" class="Symbol">(</a><a id="1580" href="foundation.univalent-type-families.html#1580" class="Bound">x</a> <a id="1582" href="foundation.univalent-type-families.html#1582" class="Bound">y</a> <a id="1584" class="Symbol">:</a> <a id="1586" href="foundation.univalent-type-families.html#1572" class="Bound">A</a><a id="1587" class="Symbol">)</a> <a id="1589" class="Symbol">→</a> <a id="1591" href="foundation-core.equivalences.html#1532" class="Function">is-equiv</a> <a id="1600" class="Symbol">(λ</a> <a id="1603" class="Symbol">(</a><a id="1604" href="foundation.univalent-type-families.html#1604" class="Bound">p</a> <a id="1606" class="Symbol">:</a> <a id="1608" href="foundation.univalent-type-families.html#1580" class="Bound">x</a> <a id="1610" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1612" href="foundation.univalent-type-families.html#1582" class="Bound">y</a><a id="1613" class="Symbol">)</a> <a id="1615" class="Symbol">→</a> <a id="1617" href="foundation.transport-along-identifications.html#1505" class="Function">equiv-tr</a> <a id="1626" href="foundation.univalent-type-families.html#1575" class="Bound">B</a> <a id="1628" href="foundation.univalent-type-families.html#1604" class="Bound">p</a><a id="1629" class="Symbol">)</a>

<a id="1632" class="Keyword">module</a> <a id="1639" href="foundation.univalent-type-families.html#1639" class="Module">_</a>
  <a id="1643" class="Symbol">{</a><a id="1644" href="foundation.univalent-type-families.html#1644" class="Bound">l1</a> <a id="1647" href="foundation.univalent-type-families.html#1647" class="Bound">l2</a> <a id="1650" class="Symbol">:</a> <a id="1652" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1657" class="Symbol">}</a> <a id="1659" class="Symbol">{</a><a id="1660" href="foundation.univalent-type-families.html#1660" class="Bound">A</a> <a id="1662" class="Symbol">:</a> <a id="1664" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1667" href="foundation.univalent-type-families.html#1644" class="Bound">l1</a><a id="1669" class="Symbol">}</a> <a id="1671" class="Symbol">{</a><a id="1672" href="foundation.univalent-type-families.html#1672" class="Bound">B</a> <a id="1674" class="Symbol">:</a> <a id="1676" href="foundation.univalent-type-families.html#1660" class="Bound">A</a> <a id="1678" class="Symbol">→</a> <a id="1680" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1683" href="foundation.univalent-type-families.html#1647" class="Bound">l2</a><a id="1685" class="Symbol">}</a>
  <a id="1689" class="Keyword">where</a>

  <a id="1698" href="foundation.univalent-type-families.html#1698" class="Function">is-prop-is-univalent</a> <a id="1719" class="Symbol">:</a> <a id="1721" href="foundation-core.propositions.html#1029" class="Function">is-prop</a> <a id="1729" class="Symbol">(</a><a id="1730" href="foundation.univalent-type-families.html#1480" class="Function">is-univalent</a> <a id="1743" href="foundation.univalent-type-families.html#1672" class="Bound">B</a><a id="1744" class="Symbol">)</a>
  <a id="1748" href="foundation.univalent-type-families.html#1698" class="Function">is-prop-is-univalent</a> <a id="1769" class="Symbol">=</a>
    <a id="1775" href="foundation.iterated-dependent-product-types.html#5476" class="Function">is-prop-iterated-Π</a> <a id="1794" class="Number">2</a> <a id="1796" class="Symbol">(λ</a> <a id="1799" href="foundation.univalent-type-families.html#1799" class="Bound">x</a> <a id="1801" href="foundation.univalent-type-families.html#1801" class="Bound">y</a> <a id="1803" class="Symbol">→</a> <a id="1805" href="foundation.equivalences.html#4866" class="Function">is-property-is-equiv</a> <a id="1826" class="Symbol">(</a><a id="1827" href="foundation.transport-along-identifications.html#1505" class="Function">equiv-tr</a> <a id="1836" href="foundation.univalent-type-families.html#1672" class="Bound">B</a><a id="1837" class="Symbol">))</a>

  <a id="1843" href="foundation.univalent-type-families.html#1843" class="Function">is-univalent-Prop</a> <a id="1861" class="Symbol">:</a> <a id="1863" href="foundation-core.propositions.html#1153" class="Function">Prop</a> <a id="1868" class="Symbol">(</a><a id="1869" href="foundation.univalent-type-families.html#1644" class="Bound">l1</a> <a id="1872" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1874" href="foundation.univalent-type-families.html#1647" class="Bound">l2</a><a id="1876" class="Symbol">)</a>
  <a id="1880" href="foundation.dependent-pair-types.html#681" class="Field">pr1</a> <a id="1884" href="foundation.univalent-type-families.html#1843" class="Function">is-univalent-Prop</a> <a id="1902" class="Symbol">=</a> <a id="1904" href="foundation.univalent-type-families.html#1480" class="Function">is-univalent</a> <a id="1917" href="foundation.univalent-type-families.html#1672" class="Bound">B</a>
  <a id="1921" href="foundation.dependent-pair-types.html#693" class="Field">pr2</a> <a id="1925" href="foundation.univalent-type-families.html#1843" class="Function">is-univalent-Prop</a> <a id="1943" class="Symbol">=</a> <a id="1945" href="foundation.univalent-type-families.html#1698" class="Function">is-prop-is-univalent</a>
</pre>
### Univalent type families

<pre class="Agda"><a id="univalent-type-family"></a><a id="2008" href="foundation.univalent-type-families.html#2008" class="Function">univalent-type-family</a> <a id="2030" class="Symbol">:</a>
  <a id="2034" class="Symbol">{</a><a id="2035" href="foundation.univalent-type-families.html#2035" class="Bound">l1</a> <a id="2038" class="Symbol">:</a> <a id="2040" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2045" class="Symbol">}</a> <a id="2047" class="Symbol">(</a><a id="2048" href="foundation.univalent-type-families.html#2048" class="Bound">l2</a> <a id="2051" class="Symbol">:</a> <a id="2053" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2058" class="Symbol">)</a> <a id="2060" class="Symbol">(</a><a id="2061" href="foundation.univalent-type-families.html#2061" class="Bound">A</a> <a id="2063" class="Symbol">:</a> <a id="2065" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2068" href="foundation.univalent-type-families.html#2035" class="Bound">l1</a><a id="2070" class="Symbol">)</a> <a id="2072" class="Symbol">→</a> <a id="2074" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2077" class="Symbol">(</a><a id="2078" href="foundation.univalent-type-families.html#2035" class="Bound">l1</a> <a id="2081" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2083" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2088" href="foundation.univalent-type-families.html#2048" class="Bound">l2</a><a id="2090" class="Symbol">)</a>
<a id="2092" href="foundation.univalent-type-families.html#2008" class="Function">univalent-type-family</a> <a id="2114" href="foundation.univalent-type-families.html#2114" class="Bound">l2</a> <a id="2117" href="foundation.univalent-type-families.html#2117" class="Bound">A</a> <a id="2119" class="Symbol">=</a> <a id="2121" href="foundation.dependent-pair-types.html#583" class="Record">Σ</a> <a id="2123" class="Symbol">(</a><a id="2124" href="foundation.univalent-type-families.html#2117" class="Bound">A</a> <a id="2126" class="Symbol">→</a> <a id="2128" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2131" href="foundation.univalent-type-families.html#2114" class="Bound">l2</a><a id="2133" class="Symbol">)</a> <a id="2135" href="foundation.univalent-type-families.html#1480" class="Function">is-univalent</a>
</pre>
## Properties

### The univalence axiom states that the identity family `id : 𝒰 → 𝒰` is univalent

<pre class="Agda"><a id="is-univalent-UU"></a><a id="2260" href="foundation.univalent-type-families.html#2260" class="Function">is-univalent-UU</a> <a id="2276" class="Symbol">:</a>
  <a id="2280" class="Symbol">(</a><a id="2281" href="foundation.univalent-type-families.html#2281" class="Bound">l</a> <a id="2283" class="Symbol">:</a> <a id="2285" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2290" class="Symbol">)</a> <a id="2292" class="Symbol">→</a> <a id="2294" href="foundation.univalent-type-families.html#1480" class="Function">is-univalent</a> <a id="2307" class="Symbol">(</a><a id="2308" href="foundation-core.function-types.html#307" class="Function">id</a> <a id="2311" class="Symbol">{</a><a id="2312" class="Argument">A</a> <a id="2314" class="Symbol">=</a> <a id="2316" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2319" href="foundation.univalent-type-families.html#2281" class="Bound">l</a><a id="2320" class="Symbol">})</a>
<a id="2323" href="foundation.univalent-type-families.html#2260" class="Function">is-univalent-UU</a> <a id="2339" href="foundation.univalent-type-families.html#2339" class="Bound">l</a> <a id="2341" class="Symbol">=</a> <a id="2343" href="foundation.univalence.html#2111" class="Function">univalence</a>
</pre>
### Assuming the univalence axiom, type families are univalent if and only if they are embeddings as maps

**Proof:** We have the
[commuting triangle of maps](foundation-core.commuting-triangles-of-maps.md)

```text
                ap B
       (x ＝ y) -----> (B x ＝ B y)
           \               /
            \             /
  equiv-tr B \           / equiv-eq
              ∨         ∨
              (B x ≃ B y)
```

where the right edge is an equivalence by the univalence axiom. Hence, the top
map is an equivalence if and only if the left map is.

<pre class="Agda"><a id="2922" class="Keyword">module</a> <a id="2929" href="foundation.univalent-type-families.html#2929" class="Module">_</a>
  <a id="2933" class="Symbol">{</a><a id="2934" href="foundation.univalent-type-families.html#2934" class="Bound">l1</a> <a id="2937" href="foundation.univalent-type-families.html#2937" class="Bound">l2</a> <a id="2940" class="Symbol">:</a> <a id="2942" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2947" class="Symbol">}</a> <a id="2949" class="Symbol">{</a><a id="2950" href="foundation.univalent-type-families.html#2950" class="Bound">A</a> <a id="2952" class="Symbol">:</a> <a id="2954" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2957" href="foundation.univalent-type-families.html#2934" class="Bound">l1</a><a id="2959" class="Symbol">}</a> <a id="2961" class="Symbol">{</a><a id="2962" href="foundation.univalent-type-families.html#2962" class="Bound">B</a> <a id="2964" class="Symbol">:</a> <a id="2966" href="foundation.univalent-type-families.html#2950" class="Bound">A</a> <a id="2968" class="Symbol">→</a> <a id="2970" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2973" href="foundation.univalent-type-families.html#2937" class="Bound">l2</a><a id="2975" class="Symbol">}</a>
  <a id="2979" class="Keyword">where</a>

  <a id="2988" class="Keyword">abstract</a>
    <a id="3001" href="foundation.univalent-type-families.html#3001" class="Function">is-emb-is-univalent</a> <a id="3021" class="Symbol">:</a>
      <a id="3029" href="foundation.univalent-type-families.html#1480" class="Function">is-univalent</a> <a id="3042" href="foundation.univalent-type-families.html#2962" class="Bound">B</a> <a id="3044" class="Symbol">→</a> <a id="3046" href="foundation-core.embeddings.html#1086" class="Function">is-emb</a> <a id="3053" href="foundation.univalent-type-families.html#2962" class="Bound">B</a>
    <a id="3059" href="foundation.univalent-type-families.html#3001" class="Function">is-emb-is-univalent</a> <a id="3079" href="foundation.univalent-type-families.html#3079" class="Bound">U</a> <a id="3081" href="foundation.univalent-type-families.html#3081" class="Bound">x</a> <a id="3083" href="foundation.univalent-type-families.html#3083" class="Bound">y</a> <a id="3085" class="Symbol">=</a>
      <a id="3093" href="foundation-core.equivalences.html#12227" class="Function">is-equiv-top-map-triangle</a>
        <a id="3127" class="Symbol">(</a> <a id="3129" href="foundation.transport-along-identifications.html#1505" class="Function">equiv-tr</a> <a id="3138" href="foundation.univalent-type-families.html#2962" class="Bound">B</a><a id="3139" class="Symbol">)</a>
        <a id="3149" class="Symbol">(</a> <a id="3151" href="foundation-core.univalence.html#1454" class="Function">equiv-eq</a><a id="3159" class="Symbol">)</a>
        <a id="3169" class="Symbol">(</a> <a id="3171" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="3174" href="foundation.univalent-type-families.html#2962" class="Bound">B</a><a id="3175" class="Symbol">)</a>
        <a id="3185" class="Symbol">(</a> <a id="3187" class="Symbol">λ</a> <a id="3189" class="Keyword">where</a> <a id="3195" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="3200" class="Symbol">→</a> <a id="3202" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="3206" class="Symbol">)</a>
        <a id="3216" class="Symbol">(</a> <a id="3218" href="foundation.univalence.html#2111" class="Function">univalence</a> <a id="3229" class="Symbol">(</a><a id="3230" href="foundation.univalent-type-families.html#2962" class="Bound">B</a> <a id="3232" href="foundation.univalent-type-families.html#3081" class="Bound">x</a><a id="3233" class="Symbol">)</a> <a id="3235" class="Symbol">(</a><a id="3236" href="foundation.univalent-type-families.html#2962" class="Bound">B</a> <a id="3238" href="foundation.univalent-type-families.html#3083" class="Bound">y</a><a id="3239" class="Symbol">))</a>
        <a id="3250" class="Symbol">(</a> <a id="3252" href="foundation.univalent-type-families.html#3079" class="Bound">U</a> <a id="3254" href="foundation.univalent-type-families.html#3081" class="Bound">x</a> <a id="3256" href="foundation.univalent-type-families.html#3083" class="Bound">y</a><a id="3257" class="Symbol">)</a>

    <a id="3264" href="foundation.univalent-type-families.html#3264" class="Function">is-univalent-is-emb</a> <a id="3284" class="Symbol">:</a>
      <a id="3292" href="foundation-core.embeddings.html#1086" class="Function">is-emb</a> <a id="3299" href="foundation.univalent-type-families.html#2962" class="Bound">B</a> <a id="3301" class="Symbol">→</a> <a id="3303" href="foundation.univalent-type-families.html#1480" class="Function">is-univalent</a> <a id="3316" href="foundation.univalent-type-families.html#2962" class="Bound">B</a>
    <a id="3322" href="foundation.univalent-type-families.html#3264" class="Function">is-univalent-is-emb</a> <a id="3342" href="foundation.univalent-type-families.html#3342" class="Bound">is-emb-B</a> <a id="3351" href="foundation.univalent-type-families.html#3351" class="Bound">x</a> <a id="3353" href="foundation.univalent-type-families.html#3353" class="Bound">y</a> <a id="3355" class="Symbol">=</a>
      <a id="3363" href="foundation-core.equivalences.html#10197" class="Function">is-equiv-left-map-triangle</a>
        <a id="3398" class="Symbol">(</a> <a id="3400" href="foundation.transport-along-identifications.html#1505" class="Function">equiv-tr</a> <a id="3409" href="foundation.univalent-type-families.html#2962" class="Bound">B</a><a id="3410" class="Symbol">)</a>
        <a id="3420" class="Symbol">(</a> <a id="3422" href="foundation-core.univalence.html#1454" class="Function">equiv-eq</a><a id="3430" class="Symbol">)</a>
        <a id="3440" class="Symbol">(</a> <a id="3442" href="foundation.action-on-identifications-functions.html#730" class="Function">ap</a> <a id="3445" href="foundation.univalent-type-families.html#2962" class="Bound">B</a><a id="3446" class="Symbol">)</a>
        <a id="3456" class="Symbol">(</a> <a id="3458" class="Symbol">λ</a> <a id="3460" class="Keyword">where</a> <a id="3466" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="3471" class="Symbol">→</a> <a id="3473" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a><a id="3477" class="Symbol">)</a>
        <a id="3487" class="Symbol">(</a> <a id="3489" href="foundation.univalent-type-families.html#3342" class="Bound">is-emb-B</a> <a id="3498" href="foundation.univalent-type-families.html#3351" class="Bound">x</a> <a id="3500" href="foundation.univalent-type-families.html#3353" class="Bound">y</a><a id="3501" class="Symbol">)</a>
        <a id="3511" class="Symbol">(</a> <a id="3513" href="foundation.univalence.html#2111" class="Function">univalence</a> <a id="3524" class="Symbol">(</a><a id="3525" href="foundation.univalent-type-families.html#2962" class="Bound">B</a> <a id="3527" href="foundation.univalent-type-families.html#3351" class="Bound">x</a><a id="3528" class="Symbol">)</a> <a id="3530" class="Symbol">(</a><a id="3531" href="foundation.univalent-type-families.html#2962" class="Bound">B</a> <a id="3533" href="foundation.univalent-type-families.html#3353" class="Bound">y</a><a id="3534" class="Symbol">))</a>
</pre>
### Univalent type families satisfy equivalence induction

<pre class="Agda"><a id="3609" class="Keyword">module</a> <a id="3616" href="foundation.univalent-type-families.html#3616" class="Module">_</a>
  <a id="3620" class="Symbol">{</a><a id="3621" href="foundation.univalent-type-families.html#3621" class="Bound">l1</a> <a id="3624" href="foundation.univalent-type-families.html#3624" class="Bound">l2</a> <a id="3627" class="Symbol">:</a> <a id="3629" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3634" class="Symbol">}</a> <a id="3636" class="Symbol">{</a><a id="3637" href="foundation.univalent-type-families.html#3637" class="Bound">A</a> <a id="3639" class="Symbol">:</a> <a id="3641" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3644" href="foundation.univalent-type-families.html#3621" class="Bound">l1</a><a id="3646" class="Symbol">}</a> <a id="3648" class="Symbol">{</a><a id="3649" href="foundation.univalent-type-families.html#3649" class="Bound">B</a> <a id="3651" class="Symbol">:</a> <a id="3653" href="foundation.univalent-type-families.html#3637" class="Bound">A</a> <a id="3655" class="Symbol">→</a> <a id="3657" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="3660" href="foundation.univalent-type-families.html#3624" class="Bound">l2</a><a id="3662" class="Symbol">}</a>
  <a id="3666" class="Symbol">(</a><a id="3667" href="foundation.univalent-type-families.html#3667" class="Bound">U</a> <a id="3669" class="Symbol">:</a> <a id="3671" href="foundation.univalent-type-families.html#1480" class="Function">is-univalent</a> <a id="3684" href="foundation.univalent-type-families.html#3649" class="Bound">B</a><a id="3685" class="Symbol">)</a>
  <a id="3689" class="Keyword">where</a>

  <a id="3698" href="foundation.univalent-type-families.html#3698" class="Function">is-torsorial-fam-equiv-is-univalent</a> <a id="3734" class="Symbol">:</a>
    <a id="3740" class="Symbol">{</a><a id="3741" href="foundation.univalent-type-families.html#3741" class="Bound">x</a> <a id="3743" class="Symbol">:</a> <a id="3745" href="foundation.univalent-type-families.html#3637" class="Bound">A</a><a id="3746" class="Symbol">}</a> <a id="3748" class="Symbol">→</a> <a id="3750" href="foundation-core.torsorial-type-families.html#2474" class="Function">is-torsorial</a> <a id="3763" class="Symbol">(λ</a> <a id="3766" href="foundation.univalent-type-families.html#3766" class="Bound">y</a> <a id="3768" class="Symbol">→</a> <a id="3770" href="foundation.univalent-type-families.html#3649" class="Bound">B</a> <a id="3772" href="foundation.univalent-type-families.html#3741" class="Bound">x</a> <a id="3774" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="3776" href="foundation.univalent-type-families.html#3649" class="Bound">B</a> <a id="3778" href="foundation.univalent-type-families.html#3766" class="Bound">y</a><a id="3779" class="Symbol">)</a>
  <a id="3783" href="foundation.univalent-type-families.html#3698" class="Function">is-torsorial-fam-equiv-is-univalent</a> <a id="3819" class="Symbol">{</a><a id="3820" href="foundation.univalent-type-families.html#3820" class="Bound">x</a><a id="3821" class="Symbol">}</a> <a id="3823" class="Symbol">=</a>
    <a id="3829" href="foundation.fundamental-theorem-of-identity-types.html#2304" class="Function">fundamental-theorem-id&#39;</a> <a id="3853" class="Symbol">(λ</a> <a id="3856" href="foundation.univalent-type-families.html#3856" class="Bound">y</a> <a id="3858" class="Symbol">→</a> <a id="3860" href="foundation.transport-along-identifications.html#1505" class="Function">equiv-tr</a> <a id="3869" href="foundation.univalent-type-families.html#3649" class="Bound">B</a><a id="3870" class="Symbol">)</a> <a id="3872" class="Symbol">(</a><a id="3873" href="foundation.univalent-type-families.html#3667" class="Bound">U</a> <a id="3875" href="foundation.univalent-type-families.html#3820" class="Bound">x</a><a id="3876" class="Symbol">)</a>

  <a id="3881" href="foundation.univalent-type-families.html#3881" class="Function">dependent-universal-property-identity-system-fam-equiv-is-univalent</a> <a id="3949" class="Symbol">:</a>
    <a id="3955" class="Symbol">{</a><a id="3956" href="foundation.univalent-type-families.html#3956" class="Bound">x</a> <a id="3958" class="Symbol">:</a> <a id="3960" href="foundation.univalent-type-families.html#3637" class="Bound">A</a><a id="3961" class="Symbol">}</a> <a id="3963" class="Symbol">→</a>
    <a id="3969" href="foundation.universal-property-identity-systems.html#1112" class="Function">dependent-universal-property-identity-system</a> <a id="4014" class="Symbol">(λ</a> <a id="4017" href="foundation.univalent-type-families.html#4017" class="Bound">y</a> <a id="4019" class="Symbol">→</a> <a id="4021" href="foundation.univalent-type-families.html#3649" class="Bound">B</a> <a id="4023" href="foundation.univalent-type-families.html#3956" class="Bound">x</a> <a id="4025" href="foundation-core.equivalences.html#2554" class="Function Operator">≃</a> <a id="4027" href="foundation.univalent-type-families.html#3649" class="Bound">B</a> <a id="4029" href="foundation.univalent-type-families.html#4017" class="Bound">y</a><a id="4030" class="Symbol">)</a> <a id="4032" href="foundation-core.equivalences.html#3922" class="Function">id-equiv</a>
  <a id="4043" href="foundation.univalent-type-families.html#3881" class="Function">dependent-universal-property-identity-system-fam-equiv-is-univalent</a> <a id="4111" class="Symbol">{</a><a id="4112" href="foundation.univalent-type-families.html#4112" class="Bound">x</a><a id="4113" class="Symbol">}</a> <a id="4115" class="Symbol">=</a>
    <a id="4121" href="foundation.universal-property-identity-systems.html#1605" class="Function">dependent-universal-property-identity-system-is-torsorial</a>
      <a id="4185" class="Symbol">(</a> <a id="4187" href="foundation-core.equivalences.html#3922" class="Function">id-equiv</a><a id="4195" class="Symbol">)</a>
      <a id="4203" class="Symbol">(</a> <a id="4205" href="foundation.univalent-type-families.html#3698" class="Function">is-torsorial-fam-equiv-is-univalent</a> <a id="4241" class="Symbol">{</a><a id="4242" href="foundation.univalent-type-families.html#4112" class="Bound">x</a><a id="4243" class="Symbol">})</a>
</pre>
### Inclusions of subuniverses into the universe are univalent

**Note.** This proof relies on essential use of the univalence axiom.

<pre class="Agda"><a id="4394" class="Keyword">module</a> <a id="4401" href="foundation.univalent-type-families.html#4401" class="Module">_</a>
  <a id="4405" class="Symbol">{</a><a id="4406" href="foundation.univalent-type-families.html#4406" class="Bound">l1</a> <a id="4409" href="foundation.univalent-type-families.html#4409" class="Bound">l2</a> <a id="4412" class="Symbol">:</a> <a id="4414" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4419" class="Symbol">}</a> <a id="4421" class="Symbol">(</a><a id="4422" href="foundation.univalent-type-families.html#4422" class="Bound">S</a> <a id="4424" class="Symbol">:</a> <a id="4426" href="foundation.subuniverses.html#1114" class="Function">subuniverse</a> <a id="4438" href="foundation.univalent-type-families.html#4406" class="Bound">l1</a> <a id="4441" href="foundation.univalent-type-families.html#4409" class="Bound">l2</a><a id="4443" class="Symbol">)</a>
  <a id="4447" class="Keyword">where</a>

  <a id="4456" href="foundation.univalent-type-families.html#4456" class="Function">is-univalent-inclusion-subuniverse</a> <a id="4491" class="Symbol">:</a> <a id="4493" href="foundation.univalent-type-families.html#1480" class="Function">is-univalent</a> <a id="4506" class="Symbol">(</a><a id="4507" href="foundation.subuniverses.html#1720" class="Function">inclusion-subuniverse</a> <a id="4529" href="foundation.univalent-type-families.html#4422" class="Bound">S</a><a id="4530" class="Symbol">)</a>
  <a id="4534" href="foundation.univalent-type-families.html#4456" class="Function">is-univalent-inclusion-subuniverse</a> <a id="4569" class="Symbol">=</a>
    <a id="4575" href="foundation.univalent-type-families.html#3264" class="Function">is-univalent-is-emb</a> <a id="4595" class="Symbol">(</a><a id="4596" href="foundation.subuniverses.html#1984" class="Function">is-emb-inclusion-subuniverse</a> <a id="4625" href="foundation.univalent-type-families.html#4422" class="Bound">S</a><a id="4626" class="Symbol">)</a>
</pre>
## See also

- [Preunivalent type families](foundation.preunivalent-type-families.md)
- [Transport-split type families](foundation.transport-split-type-families.md):
  By a corollary of
  [the fundamental theorem of identity types](foundation.fundamental-theorem-of-identity-types.md),
  `equiv-tr B` is a
  [fiberwise equivalence](foundation-core.families-of-equivalences.md) as soon
  as it admits a fiberwise [section](foundation-core.sections.md).