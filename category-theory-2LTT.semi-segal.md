# Semi-Segal types

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="category-theory-2LTT.semi-segal.html" class="Module">category-theory-2LTT.semi-segal</a> <a id="68" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="124" class="Keyword">open</a> <a id="129" class="Keyword">import</a> <a id="136" href="category-theory.cones-precategories%25E1%25B5%2589.html" class="Module">category-theory.cones-precategoriesᵉ</a>
<a id="173" class="Keyword">open</a> <a id="178" class="Keyword">import</a> <a id="185" href="category-theory.constant-functors%25E1%25B5%2589.html" class="Module">category-theory.constant-functorsᵉ</a>
<a id="220" class="Keyword">open</a> <a id="225" class="Keyword">import</a> <a id="232" href="category-theory.copresheaf-categories%25E1%25B5%2589.html" class="Module">category-theory.copresheaf-categoriesᵉ</a>
<a id="271" class="Keyword">open</a> <a id="276" class="Keyword">import</a> <a id="283" href="category-theory.functors-precategories%25E1%25B5%2589.html" class="Module">category-theory.functors-precategoriesᵉ</a>
<a id="323" class="Keyword">open</a> <a id="328" class="Keyword">import</a> <a id="335" href="category-theory.isomorphisms-in-precategories%25E1%25B5%2589.html" class="Module">category-theory.isomorphisms-in-precategoriesᵉ</a>
<a id="382" class="Keyword">open</a> <a id="387" class="Keyword">import</a> <a id="394" href="category-theory.limits-precategories%25E1%25B5%2589.html" class="Module">category-theory.limits-precategoriesᵉ</a>
<a id="432" class="Keyword">open</a> <a id="437" class="Keyword">import</a> <a id="444" href="category-theory.natural-transformations-functors-precategories%25E1%25B5%2589.html" class="Module">category-theory.natural-transformations-functors-precategoriesᵉ</a>
<a id="508" class="Keyword">open</a> <a id="513" class="Keyword">import</a> <a id="520" href="category-theory.precategories%25E1%25B5%2589.html" class="Module">category-theory.precategoriesᵉ</a>
<a id="551" class="Keyword">open</a> <a id="556" class="Keyword">import</a> <a id="563" href="category-theory.right-extensions-precategories%25E1%25B5%2589.html" class="Module">category-theory.right-extensions-precategoriesᵉ</a>
<a id="611" class="Keyword">open</a> <a id="616" class="Keyword">import</a> <a id="623" href="category-theory.right-kan-extensions-precategories%25E1%25B5%2589.html" class="Module">category-theory.right-kan-extensions-precategoriesᵉ</a>

<a id="676" class="Keyword">open</a> <a id="681" class="Keyword">import</a> <a id="688" href="category-theory-2LTT.inverse-precategories.html" class="Module">category-theory-2LTT.inverse-precategories</a>
<a id="731" class="Keyword">open</a> <a id="736" class="Keyword">import</a> <a id="743" href="category-theory-2LTT.matching-objects.html" class="Module">category-theory-2LTT.matching-objects</a>
<a id="781" class="Keyword">open</a> <a id="786" class="Keyword">import</a> <a id="793" href="category-theory-2LTT.reduced-coslice-precategory.html" class="Module">category-theory-2LTT.reduced-coslice-precategory</a>
<a id="842" class="Keyword">open</a> <a id="847" class="Keyword">import</a> <a id="854" href="category-theory-2LTT.reedy-fibrations.html" class="Module">category-theory-2LTT.reedy-fibrations</a>
<a id="892" class="Keyword">open</a> <a id="897" class="Keyword">import</a> <a id="904" href="category-theory-2LTT.strict-simplex-precategory.html" class="Module">category-theory-2LTT.strict-simplex-precategory</a>

<a id="953" class="Keyword">open</a> <a id="958" class="Keyword">import</a> <a id="965" href="elementary-number-theory.inequality-natural-numbers%25E1%25B5%2589.html" class="Module">elementary-number-theory.inequality-natural-numbersᵉ</a>
<a id="1018" class="Keyword">open</a> <a id="1023" class="Keyword">import</a> <a id="1030" href="elementary-number-theory.natural-numbers%25E1%25B5%2589.html" class="Module">elementary-number-theory.natural-numbersᵉ</a>
<a id="1072" class="Keyword">open</a> <a id="1077" class="Keyword">import</a> <a id="1084" href="elementary-number-theory.strict-inequality-natural-numbers%25E1%25B5%2589.html" class="Module">elementary-number-theory.strict-inequality-natural-numbersᵉ</a>

<a id="1145" class="Keyword">open</a> <a id="1150" class="Keyword">import</a> <a id="1157" href="foundation.action-on-identifications-functions%25E1%25B5%2589.html" class="Module">foundation.action-on-identifications-functionsᵉ</a>
<a id="1205" class="Keyword">open</a> <a id="1210" class="Keyword">import</a> <a id="1217" href="foundation.category-of-sets%25E1%25B5%2589.html" class="Module">foundation.category-of-setsᵉ</a>
<a id="1246" class="Keyword">open</a> <a id="1251" class="Keyword">import</a> <a id="1258" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="1291" class="Keyword">open</a> <a id="1296" class="Keyword">import</a> <a id="1303" href="foundation.equivalences%25E1%25B5%2589.html" class="Module">foundation.equivalencesᵉ</a>
<a id="1328" class="Keyword">open</a> <a id="1333" class="Keyword">import</a> <a id="1340" href="foundation.fibers-of-maps%25E1%25B5%2589.html" class="Module">foundation.fibers-of-mapsᵉ</a>
<a id="1367" class="Keyword">open</a> <a id="1372" class="Keyword">import</a> <a id="1379" href="foundation.function-extensionality%25E1%25B5%2589.html" class="Module">foundation.function-extensionalityᵉ</a>
<a id="1415" class="Keyword">open</a> <a id="1420" class="Keyword">import</a> <a id="1427" href="foundation.function-types%25E1%25B5%2589.html" class="Module">foundation.function-typesᵉ</a>
<a id="1454" class="Keyword">open</a> <a id="1459" class="Keyword">import</a> <a id="1466" href="foundation.identity-types%25E1%25B5%2589.html" class="Module">foundation.identity-typesᵉ</a>
<a id="1493" class="Keyword">open</a> <a id="1498" class="Keyword">import</a> <a id="1505" href="foundation.sets%25E1%25B5%2589.html" class="Module">foundation.setsᵉ</a>
<a id="1522" class="Keyword">open</a> <a id="1527" class="Keyword">import</a> <a id="1534" href="foundation.standard-pullbacks%25E1%25B5%2589.html" class="Module">foundation.standard-pullbacksᵉ</a>
<a id="1565" class="Keyword">open</a> <a id="1570" class="Keyword">import</a> <a id="1577" href="foundation.unit-type%25E1%25B5%2589.html" class="Module">foundation.unit-typeᵉ</a>
<a id="1599" class="Keyword">open</a> <a id="1604" class="Keyword">import</a> <a id="1611" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="1640" class="Keyword">open</a> <a id="1645" class="Keyword">import</a> <a id="1652" href="foundation-2LTT.fibrant-types.html" class="Module">foundation-2LTT.fibrant-types</a>
<a id="1682" class="Keyword">open</a> <a id="1687" class="Keyword">import</a> <a id="1694" href="foundation-2LTT.fibrations.html" class="Module">foundation-2LTT.fibrations</a>
</pre>
</details>

## Definitions

### Semi segal

<pre class="Agda"><a id="1778" class="Keyword">module</a> <a id="1785" href="category-theory-2LTT.semi-segal.html#1785" class="Module">_</a>
  <a id="1789" class="Symbol">(</a><a id="1790" href="category-theory-2LTT.semi-segal.html#1790" class="Bound">X</a> <a id="1792" class="Symbol">:</a> <a id="1794" href="category-theory-2LTT.reedy-fibrations.html#3805" class="Function">Reedy-Fibrant-Semisimplicial-Type</a><a id="1827" class="Symbol">)</a>
  <a id="1831" class="Keyword">where</a>

  <a id="1840" href="category-theory-2LTT.semi-segal.html#1840" class="Function">is-semi-segal</a> <a id="1854" class="Symbol">:</a> <a id="1856" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1860" class="Symbol">(</a><a id="1861" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1866" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="1871" class="Symbol">)</a>
  <a id="1875" href="category-theory-2LTT.semi-segal.html#1840" class="Function">is-semi-segal</a> <a id="1889" class="Symbol">=</a>
    <a id="1895" class="Symbol">(</a><a id="1896" href="category-theory-2LTT.semi-segal.html#1896" class="Bound">k</a> <a id="1898" href="category-theory-2LTT.semi-segal.html#1898" class="Bound">n</a> <a id="1900" class="Symbol">:</a> <a id="1902" href="elementary-number-theory.natural-numbers%25E1%25B5%2589.html#783" class="Datatype">ℕᵉ</a><a id="1904" class="Symbol">)</a> <a id="1906" class="Symbol">→</a> <a id="1908" href="elementary-number-theory.strict-inequality-natural-numbers%25E1%25B5%2589.html#1342" class="Function">le-ℕᵉ</a> <a id="1914" href="elementary-number-theory.natural-numbers%25E1%25B5%2589.html#848" class="InductiveConstructor">0ᵉ</a> <a id="1917" href="category-theory-2LTT.semi-segal.html#1896" class="Bound">k</a> <a id="1919" class="Symbol">→</a> <a id="1921" href="elementary-number-theory.strict-inequality-natural-numbers%25E1%25B5%2589.html#1342" class="Function">le-ℕᵉ</a> <a id="1927" href="category-theory-2LTT.semi-segal.html#1896" class="Bound">k</a> <a id="1929" href="category-theory-2LTT.semi-segal.html#1898" class="Bound">n</a> <a id="1931" class="Symbol">→</a>
    <a id="1937" href="foundation-2LTT.fibrations.html#846" class="Function">is-trivial-fibration</a>
      <a id="1964" class="Symbol">λ</a> <a id="1966" href="category-theory-2LTT.semi-segal.html#1966" class="Bound">τ</a> <a id="1968" class="Symbol">→</a>
        <a id="1978" href="category-theory.natural-transformations-functors-precategories%25E1%25B5%2589.html#3289" class="Function">comp-natural-transformation-Precategoryᵉ</a>
          <a id="2029" class="Symbol">(</a> <a id="2031" href="category-theory-2LTT.strict-simplex-precategory.html#3795" class="Function">op-strict-simplex-Precategoryᵉ</a><a id="2061" class="Symbol">)</a>
          <a id="2073" class="Symbol">(</a> <a id="2075" href="foundation.category-of-sets%25E1%25B5%2589.html#3733" class="Function">Set-Precategoryᵉ</a> <a id="2092" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="2097" class="Symbol">)</a>
          <a id="2109" class="Symbol">(</a> <a id="2111" href="category-theory-2LTT.strict-simplex-precategory.html#7807" class="Function">horn-strict-simplex</a> <a id="2131" href="category-theory-2LTT.semi-segal.html#1896" class="Bound">k</a> <a id="2133" href="category-theory-2LTT.semi-segal.html#1898" class="Bound">n</a><a id="2134" class="Symbol">)</a>
          <a id="2146" class="Symbol">(</a> <a id="2148" href="category-theory-2LTT.strict-simplex-precategory.html#5870" class="Function">standard-strict-simplex</a> <a id="2172" href="category-theory-2LTT.semi-segal.html#1898" class="Bound">n</a><a id="2173" class="Symbol">)</a>
          <a id="2185" class="Symbol">(</a> <a id="2187" href="category-theory-2LTT.reedy-fibrations.html#4087" class="Function">diagram-Reedy-Fibrant-Semisimplicial-Type</a> <a id="2229" href="category-theory-2LTT.semi-segal.html#1790" class="Bound">X</a><a id="2230" class="Symbol">)</a>
          <a id="2242" class="Symbol">(</a> <a id="2244" href="category-theory-2LTT.semi-segal.html#1966" class="Bound">τ</a><a id="2245" class="Symbol">)</a>
          <a id="2257" class="Symbol">(</a> <a id="2259" href="category-theory-2LTT.strict-simplex-precategory.html#8770" class="Function">horn-inclusion-strict-simplex</a> <a id="2289" href="category-theory-2LTT.semi-segal.html#1896" class="Bound">k</a> <a id="2291" href="category-theory-2LTT.semi-segal.html#1898" class="Bound">n</a><a id="2292" class="Symbol">)</a>

<a id="Semi-Segal"></a><a id="2295" href="category-theory-2LTT.semi-segal.html#2295" class="Function">Semi-Segal</a> <a id="2306" class="Symbol">:</a> <a id="2308" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2312" class="Symbol">(</a><a id="2313" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="2318" href="Agda.Primitive.html#915" class="Primitive">lzero</a><a id="2323" class="Symbol">)</a>
<a id="2325" href="category-theory-2LTT.semi-segal.html#2295" class="Function">Semi-Segal</a> <a id="2336" class="Symbol">=</a>
  <a id="2340" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="2343" href="category-theory-2LTT.reedy-fibrations.html#3805" class="Function">Reedy-Fibrant-Semisimplicial-Type</a> <a id="2377" href="category-theory-2LTT.semi-segal.html#1840" class="Function">is-semi-segal</a>

<a id="2392" class="Keyword">module</a> <a id="2399" href="category-theory-2LTT.semi-segal.html#2399" class="Module">_</a>
  <a id="2403" class="Symbol">(</a><a id="2404" href="category-theory-2LTT.semi-segal.html#2404" class="Bound">X</a> <a id="2406" class="Symbol">:</a> <a id="2408" href="category-theory-2LTT.semi-segal.html#2295" class="Function">Semi-Segal</a><a id="2418" class="Symbol">)</a>
  <a id="2422" class="Keyword">where</a>

  <a id="2431" href="category-theory-2LTT.semi-segal.html#2431" class="Function">reedy-fibrant-semisimplicial-type-Semi-Segal</a> <a id="2476" class="Symbol">:</a>
    <a id="2482" href="category-theory-2LTT.reedy-fibrations.html#3805" class="Function">Reedy-Fibrant-Semisimplicial-Type</a>
  <a id="2518" href="category-theory-2LTT.semi-segal.html#2431" class="Function">reedy-fibrant-semisimplicial-type-Semi-Segal</a> <a id="2563" class="Symbol">=</a> <a id="2565" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="2570" href="category-theory-2LTT.semi-segal.html#2404" class="Bound">X</a>

  <a id="2575" href="category-theory-2LTT.semi-segal.html#2575" class="Function">diagram-Semi-Segal</a> <a id="2594" class="Symbol">:</a>
    <a id="2600" href="category-theory.copresheaf-categories%25E1%25B5%2589.html#3314" class="Function">copresheaf-Precategoryᵉ</a> <a id="2624" href="category-theory-2LTT.strict-simplex-precategory.html#3795" class="Function">op-strict-simplex-Precategoryᵉ</a> <a id="2655" href="Agda.Primitive.html#915" class="Primitive">lzero</a>
  <a id="2663" href="category-theory-2LTT.semi-segal.html#2575" class="Function">diagram-Semi-Segal</a> <a id="2682" class="Symbol">=</a>
    <a id="2688" href="category-theory-2LTT.reedy-fibrations.html#4087" class="Function">diagram-Reedy-Fibrant-Semisimplicial-Type</a>
      <a id="2736" href="category-theory-2LTT.semi-segal.html#2431" class="Function">reedy-fibrant-semisimplicial-type-Semi-Segal</a>

  <a id="2784" href="category-theory-2LTT.semi-segal.html#2784" class="Function">is-reedy-fibrant-Semi-Segal</a> <a id="2812" class="Symbol">:</a>
    <a id="2818" href="category-theory-2LTT.reedy-fibrations.html#3317" class="Function">is-reedy-fibrant</a> <a id="2835" href="category-theory-2LTT.strict-simplex-precategory.html#3795" class="Function">op-strict-simplex-Precategoryᵉ</a> <a id="2866" href="category-theory-2LTT.semi-segal.html#2575" class="Function">diagram-Semi-Segal</a>
  <a id="2887" href="category-theory-2LTT.semi-segal.html#2784" class="Function">is-reedy-fibrant-Semi-Segal</a> <a id="2915" class="Symbol">=</a>
    <a id="2921" href="category-theory-2LTT.reedy-fibrations.html#4252" class="Function">is-reedy-fibrant-Reedy-Fibrant-Semisimplicial-Type</a>
      <a id="2978" href="category-theory-2LTT.semi-segal.html#2431" class="Function">reedy-fibrant-semisimplicial-type-Semi-Segal</a>

  <a id="3026" href="category-theory-2LTT.semi-segal.html#3026" class="Function">is-semi-segal-Semi-Segal</a> <a id="3051" class="Symbol">:</a>
    <a id="3057" href="category-theory-2LTT.semi-segal.html#1840" class="Function">is-semi-segal</a> <a id="3071" href="category-theory-2LTT.semi-segal.html#2431" class="Function">reedy-fibrant-semisimplicial-type-Semi-Segal</a>
  <a id="3118" href="category-theory-2LTT.semi-segal.html#3026" class="Function">is-semi-segal-Semi-Segal</a> <a id="3143" class="Symbol">=</a> <a id="3145" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="3150" href="category-theory-2LTT.semi-segal.html#2404" class="Bound">X</a>

  <a id="3155" href="category-theory-2LTT.semi-segal.html#3155" class="Function">horn-filler-Semi-Segal</a> <a id="3178" class="Symbol">:</a>
    <a id="3184" class="Symbol">(</a><a id="3185" href="category-theory-2LTT.semi-segal.html#3185" class="Bound">k</a> <a id="3187" href="category-theory-2LTT.semi-segal.html#3187" class="Bound">n</a> <a id="3189" class="Symbol">:</a> <a id="3191" href="elementary-number-theory.natural-numbers%25E1%25B5%2589.html#783" class="Datatype">ℕᵉ</a><a id="3193" class="Symbol">)</a> <a id="3195" class="Symbol">→</a> <a id="3197" href="elementary-number-theory.strict-inequality-natural-numbers%25E1%25B5%2589.html#1342" class="Function">le-ℕᵉ</a> <a id="3203" href="elementary-number-theory.natural-numbers%25E1%25B5%2589.html#848" class="InductiveConstructor">0ᵉ</a> <a id="3206" href="category-theory-2LTT.semi-segal.html#3185" class="Bound">k</a> <a id="3208" class="Symbol">→</a> <a id="3210" href="elementary-number-theory.strict-inequality-natural-numbers%25E1%25B5%2589.html#1342" class="Function">le-ℕᵉ</a> <a id="3216" href="category-theory-2LTT.semi-segal.html#3185" class="Bound">k</a> <a id="3218" href="category-theory-2LTT.semi-segal.html#3187" class="Bound">n</a> <a id="3220" class="Symbol">→</a>
    <a id="3226" href="category-theory-2LTT.strict-simplex-precategory.html#8241" class="Function">strict-simplicial-map</a>
      <a id="3254" class="Symbol">(</a><a id="3255" href="category-theory-2LTT.strict-simplex-precategory.html#7807" class="Function">horn-strict-simplex</a> <a id="3275" href="category-theory-2LTT.semi-segal.html#3185" class="Bound">k</a> <a id="3277" href="category-theory-2LTT.semi-segal.html#3187" class="Bound">n</a><a id="3278" class="Symbol">)</a>
      <a id="3286" class="Symbol">(</a><a id="3287" href="category-theory-2LTT.semi-segal.html#2575" class="Function">diagram-Semi-Segal</a><a id="3305" class="Symbol">)</a> <a id="3307" class="Symbol">→</a>
    <a id="3313" href="category-theory-2LTT.strict-simplex-precategory.html#8241" class="Function">strict-simplicial-map</a>
      <a id="3341" class="Symbol">(</a><a id="3342" href="category-theory-2LTT.strict-simplex-precategory.html#5870" class="Function">standard-strict-simplex</a> <a id="3366" href="category-theory-2LTT.semi-segal.html#3187" class="Bound">n</a><a id="3367" class="Symbol">)</a>
      <a id="3375" class="Symbol">(</a><a id="3376" href="category-theory-2LTT.semi-segal.html#2575" class="Function">diagram-Semi-Segal</a><a id="3394" class="Symbol">)</a>
  <a id="3398" href="category-theory-2LTT.semi-segal.html#3155" class="Function">horn-filler-Semi-Segal</a> <a id="3421" href="category-theory-2LTT.semi-segal.html#3421" class="Bound">k</a> <a id="3423" href="category-theory-2LTT.semi-segal.html#3423" class="Bound">n</a> <a id="3425" href="category-theory-2LTT.semi-segal.html#3425" class="Bound">0&lt;k</a> <a id="3429" href="category-theory-2LTT.semi-segal.html#3429" class="Bound">k&lt;n</a> <a id="3433" href="category-theory-2LTT.semi-segal.html#3433" class="Bound">τ</a> <a id="3435" class="Symbol">=</a>
    <a id="3441" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="3446" class="Symbol">(</a><a id="3447" href="foundation-2LTT.fibrant-types.html#6615" class="Function">center-is-trivially-fibrant</a> <a id="3475" class="Symbol">(</a><a id="3476" href="category-theory-2LTT.semi-segal.html#3026" class="Function">is-semi-segal-Semi-Segal</a> <a id="3501" href="category-theory-2LTT.semi-segal.html#3421" class="Bound">k</a> <a id="3503" href="category-theory-2LTT.semi-segal.html#3423" class="Bound">n</a> <a id="3505" href="category-theory-2LTT.semi-segal.html#3425" class="Bound">0&lt;k</a> <a id="3509" href="category-theory-2LTT.semi-segal.html#3429" class="Bound">k&lt;n</a> <a id="3513" href="category-theory-2LTT.semi-segal.html#3433" class="Bound">τ</a><a id="3514" class="Symbol">))</a>
</pre>