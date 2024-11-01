# Cospans of types

<pre class="Agda"><a id="29" class="Keyword">module</a> <a id="36" href="foundation.cospans%25E1%25B5%2589.html" class="Module">foundation.cospansᵉ</a> <a id="56" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="112" class="Keyword">open</a> <a id="117" class="Keyword">import</a> <a id="124" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="157" class="Keyword">open</a> <a id="162" class="Keyword">import</a> <a id="169" href="foundation.fundamental-theorem-of-identity-types%25E1%25B5%2589.html" class="Module">foundation.fundamental-theorem-of-identity-typesᵉ</a>
<a id="219" class="Keyword">open</a> <a id="224" class="Keyword">import</a> <a id="231" href="foundation.homotopy-induction%25E1%25B5%2589.html" class="Module">foundation.homotopy-inductionᵉ</a>
<a id="262" class="Keyword">open</a> <a id="267" class="Keyword">import</a> <a id="274" href="foundation.structure-identity-principle%25E1%25B5%2589.html" class="Module">foundation.structure-identity-principleᵉ</a>
<a id="315" class="Keyword">open</a> <a id="320" class="Keyword">import</a> <a id="327" href="foundation.univalence%25E1%25B5%2589.html" class="Module">foundation.univalenceᵉ</a>
<a id="350" class="Keyword">open</a> <a id="355" class="Keyword">import</a> <a id="362" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="391" class="Keyword">open</a> <a id="396" class="Keyword">import</a> <a id="403" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html" class="Module">foundation-core.cartesian-product-typesᵉ</a>
<a id="444" class="Keyword">open</a> <a id="449" class="Keyword">import</a> <a id="456" href="foundation-core.commuting-triangles-of-maps%25E1%25B5%2589.html" class="Module">foundation-core.commuting-triangles-of-mapsᵉ</a>
<a id="501" class="Keyword">open</a> <a id="506" class="Keyword">import</a> <a id="513" href="foundation-core.equivalences%25E1%25B5%2589.html" class="Module">foundation-core.equivalencesᵉ</a>
<a id="543" class="Keyword">open</a> <a id="548" class="Keyword">import</a> <a id="555" href="foundation-core.function-types%25E1%25B5%2589.html" class="Module">foundation-core.function-typesᵉ</a>
<a id="587" class="Keyword">open</a> <a id="592" class="Keyword">import</a> <a id="599" href="foundation-core.homotopies%25E1%25B5%2589.html" class="Module">foundation-core.homotopiesᵉ</a>
<a id="627" class="Keyword">open</a> <a id="632" class="Keyword">import</a> <a id="639" href="foundation-core.identity-types%25E1%25B5%2589.html" class="Module">foundation-core.identity-typesᵉ</a>
<a id="671" class="Keyword">open</a> <a id="676" class="Keyword">import</a> <a id="683" href="foundation-core.torsorial-type-families%25E1%25B5%2589.html" class="Module">foundation-core.torsorial-type-familiesᵉ</a>
</pre>
</details>

## Idea

A {{#concept "cospan" Disambiguation="types" Agda=cospan}} from `A` to `B`
consists of a type `X` and maps `f : A → X` and `g : B → X`, as indicated in the
diagram

```text
      f         g
  A -----> X <----- B
```

We disambiguate between cospans and
[cospan diagrams](foundation.cospan-diagrams.md). We consider a cospan from `A`
to `B` a morphism from `A` to `B` in the category of types and cospans between
them, whereas we consider cospan diagrams to be _objects_ in the category of
diagrams of types of the form `* <---- * ----> *`. Conceptually there is a
subtle, but important distinction between cospans and cospan diagrams. Cospan
diagrams are more suitable for functorial operations that take "cospans" as
input, but for which the functorial action takes a natural transformation, i.e.,
a morphism of cospan diagrams, as input. Examples of this kind include
[pullbacks](foundation.pullbacks.md).

## Definitions

### Cospans

<pre class="Agda"><a id="cospanᵉ"></a><a id="1697" href="foundation.cospans%25E1%25B5%2589.html#1697" class="Function">cospanᵉ</a> <a id="1705" class="Symbol">:</a>
  <a id="1709" class="Symbol">{</a><a id="1710" href="foundation.cospans%25E1%25B5%2589.html#1710" class="Bound">l1ᵉ</a> <a id="1714" href="foundation.cospans%25E1%25B5%2589.html#1714" class="Bound">l2ᵉ</a> <a id="1718" class="Symbol">:</a> <a id="1720" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1725" class="Symbol">}</a> <a id="1727" class="Symbol">(</a><a id="1728" href="foundation.cospans%25E1%25B5%2589.html#1728" class="Bound">lᵉ</a> <a id="1731" class="Symbol">:</a> <a id="1733" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1738" class="Symbol">)</a> <a id="1740" class="Symbol">(</a><a id="1741" href="foundation.cospans%25E1%25B5%2589.html#1741" class="Bound">Aᵉ</a> <a id="1744" class="Symbol">:</a> <a id="1746" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1750" href="foundation.cospans%25E1%25B5%2589.html#1710" class="Bound">l1ᵉ</a><a id="1753" class="Symbol">)</a> <a id="1755" class="Symbol">(</a><a id="1756" href="foundation.cospans%25E1%25B5%2589.html#1756" class="Bound">Bᵉ</a> <a id="1759" class="Symbol">:</a> <a id="1761" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1765" href="foundation.cospans%25E1%25B5%2589.html#1714" class="Bound">l2ᵉ</a><a id="1768" class="Symbol">)</a> <a id="1770" class="Symbol">→</a>
  <a id="1774" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1778" class="Symbol">(</a><a id="1779" href="foundation.cospans%25E1%25B5%2589.html#1710" class="Bound">l1ᵉ</a> <a id="1783" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1785" href="foundation.cospans%25E1%25B5%2589.html#1714" class="Bound">l2ᵉ</a> <a id="1789" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1791" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1796" href="foundation.cospans%25E1%25B5%2589.html#1728" class="Bound">lᵉ</a><a id="1798" class="Symbol">)</a>
<a id="1800" href="foundation.cospans%25E1%25B5%2589.html#1697" class="Function">cospanᵉ</a> <a id="1808" href="foundation.cospans%25E1%25B5%2589.html#1808" class="Bound">lᵉ</a> <a id="1811" href="foundation.cospans%25E1%25B5%2589.html#1811" class="Bound">Aᵉ</a> <a id="1814" href="foundation.cospans%25E1%25B5%2589.html#1814" class="Bound">Bᵉ</a> <a id="1817" class="Symbol">=</a> <a id="1819" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="1822" class="Symbol">(</a><a id="1823" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1827" href="foundation.cospans%25E1%25B5%2589.html#1808" class="Bound">lᵉ</a><a id="1829" class="Symbol">)</a> <a id="1831" class="Symbol">(λ</a> <a id="1834" href="foundation.cospans%25E1%25B5%2589.html#1834" class="Bound">Xᵉ</a> <a id="1837" class="Symbol">→</a> <a id="1839" class="Symbol">(</a><a id="1840" href="foundation.cospans%25E1%25B5%2589.html#1811" class="Bound">Aᵉ</a> <a id="1843" class="Symbol">→</a> <a id="1845" href="foundation.cospans%25E1%25B5%2589.html#1834" class="Bound">Xᵉ</a><a id="1847" class="Symbol">)</a> <a id="1849" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#623" class="Function Operator">×ᵉ</a> <a id="1852" class="Symbol">(</a><a id="1853" href="foundation.cospans%25E1%25B5%2589.html#1814" class="Bound">Bᵉ</a> <a id="1856" class="Symbol">→</a> <a id="1858" href="foundation.cospans%25E1%25B5%2589.html#1834" class="Bound">Xᵉ</a><a id="1860" class="Symbol">))</a>

<a id="1864" class="Keyword">module</a> <a id="1871" href="foundation.cospans%25E1%25B5%2589.html#1871" class="Module">_</a>
  <a id="1875" class="Symbol">{</a><a id="1876" href="foundation.cospans%25E1%25B5%2589.html#1876" class="Bound">l1ᵉ</a> <a id="1880" href="foundation.cospans%25E1%25B5%2589.html#1880" class="Bound">l2ᵉ</a> <a id="1884" class="Symbol">:</a> <a id="1886" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1891" class="Symbol">}</a> <a id="1893" class="Symbol">{</a><a id="1894" href="foundation.cospans%25E1%25B5%2589.html#1894" class="Bound">lᵉ</a> <a id="1897" class="Symbol">:</a> <a id="1899" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1904" class="Symbol">}</a> <a id="1906" class="Symbol">{</a><a id="1907" href="foundation.cospans%25E1%25B5%2589.html#1907" class="Bound">Aᵉ</a> <a id="1910" class="Symbol">:</a> <a id="1912" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1916" href="foundation.cospans%25E1%25B5%2589.html#1876" class="Bound">l1ᵉ</a><a id="1919" class="Symbol">}</a> <a id="1921" class="Symbol">{</a><a id="1922" href="foundation.cospans%25E1%25B5%2589.html#1922" class="Bound">Bᵉ</a> <a id="1925" class="Symbol">:</a> <a id="1927" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1931" href="foundation.cospans%25E1%25B5%2589.html#1880" class="Bound">l2ᵉ</a><a id="1934" class="Symbol">}</a> <a id="1936" class="Symbol">(</a><a id="1937" href="foundation.cospans%25E1%25B5%2589.html#1937" class="Bound">cᵉ</a> <a id="1940" class="Symbol">:</a> <a id="1942" href="foundation.cospans%25E1%25B5%2589.html#1697" class="Function">cospanᵉ</a> <a id="1950" href="foundation.cospans%25E1%25B5%2589.html#1894" class="Bound">lᵉ</a> <a id="1953" href="foundation.cospans%25E1%25B5%2589.html#1907" class="Bound">Aᵉ</a> <a id="1956" href="foundation.cospans%25E1%25B5%2589.html#1922" class="Bound">Bᵉ</a><a id="1958" class="Symbol">)</a>
  <a id="1962" class="Keyword">where</a>

  <a id="1971" href="foundation.cospans%25E1%25B5%2589.html#1971" class="Function">codomain-cospanᵉ</a> <a id="1988" class="Symbol">:</a> <a id="1990" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1994" href="foundation.cospans%25E1%25B5%2589.html#1894" class="Bound">lᵉ</a>
  <a id="1999" href="foundation.cospans%25E1%25B5%2589.html#1971" class="Function">codomain-cospanᵉ</a> <a id="2016" class="Symbol">=</a> <a id="2018" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="2023" href="foundation.cospans%25E1%25B5%2589.html#1937" class="Bound">cᵉ</a>

  <a id="2029" href="foundation.cospans%25E1%25B5%2589.html#2029" class="Function">left-map-cospanᵉ</a> <a id="2046" class="Symbol">:</a> <a id="2048" href="foundation.cospans%25E1%25B5%2589.html#1907" class="Bound">Aᵉ</a> <a id="2051" class="Symbol">→</a> <a id="2053" href="foundation.cospans%25E1%25B5%2589.html#1971" class="Function">codomain-cospanᵉ</a>
  <a id="2072" href="foundation.cospans%25E1%25B5%2589.html#2029" class="Function">left-map-cospanᵉ</a> <a id="2089" class="Symbol">=</a> <a id="2091" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="2096" class="Symbol">(</a><a id="2097" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="2102" href="foundation.cospans%25E1%25B5%2589.html#1937" class="Bound">cᵉ</a><a id="2104" class="Symbol">)</a>

  <a id="2109" href="foundation.cospans%25E1%25B5%2589.html#2109" class="Function">right-map-cospanᵉ</a> <a id="2127" class="Symbol">:</a> <a id="2129" href="foundation.cospans%25E1%25B5%2589.html#1922" class="Bound">Bᵉ</a> <a id="2132" class="Symbol">→</a> <a id="2134" href="foundation.cospans%25E1%25B5%2589.html#1971" class="Function">codomain-cospanᵉ</a>
  <a id="2153" href="foundation.cospans%25E1%25B5%2589.html#2109" class="Function">right-map-cospanᵉ</a> <a id="2171" class="Symbol">=</a> <a id="2173" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="2178" class="Symbol">(</a><a id="2179" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="2184" href="foundation.cospans%25E1%25B5%2589.html#1937" class="Bound">cᵉ</a><a id="2186" class="Symbol">)</a>
</pre>
### The identity cospan

<pre class="Agda"><a id="id-cospanᵉ"></a><a id="2226" href="foundation.cospans%25E1%25B5%2589.html#2226" class="Function">id-cospanᵉ</a> <a id="2237" class="Symbol">:</a> <a id="2239" class="Symbol">{</a><a id="2240" href="foundation.cospans%25E1%25B5%2589.html#2240" class="Bound">lᵉ</a> <a id="2243" class="Symbol">:</a> <a id="2245" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2250" class="Symbol">}</a> <a id="2252" class="Symbol">(</a><a id="2253" href="foundation.cospans%25E1%25B5%2589.html#2253" class="Bound">Aᵉ</a> <a id="2256" class="Symbol">:</a> <a id="2258" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2262" href="foundation.cospans%25E1%25B5%2589.html#2240" class="Bound">lᵉ</a><a id="2264" class="Symbol">)</a> <a id="2266" class="Symbol">→</a> <a id="2268" href="foundation.cospans%25E1%25B5%2589.html#1697" class="Function">cospanᵉ</a> <a id="2276" href="foundation.cospans%25E1%25B5%2589.html#2240" class="Bound">lᵉ</a> <a id="2279" href="foundation.cospans%25E1%25B5%2589.html#2253" class="Bound">Aᵉ</a> <a id="2282" href="foundation.cospans%25E1%25B5%2589.html#2253" class="Bound">Aᵉ</a>
<a id="2285" href="foundation.cospans%25E1%25B5%2589.html#2226" class="Function">id-cospanᵉ</a> <a id="2296" href="foundation.cospans%25E1%25B5%2589.html#2296" class="Bound">Aᵉ</a> <a id="2299" class="Symbol">=</a> <a id="2301" class="Symbol">(</a><a id="2302" href="foundation.cospans%25E1%25B5%2589.html#2296" class="Bound">Aᵉ</a> <a id="2305" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2308" href="foundation-core.function-types%25E1%25B5%2589.html#309" class="Function">idᵉ</a> <a id="2312" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2315" href="foundation-core.function-types%25E1%25B5%2589.html#309" class="Function">idᵉ</a><a id="2318" class="Symbol">)</a>
</pre>
### The swapping operation on cospans

<pre class="Agda"><a id="swap-cospanᵉ"></a><a id="2372" href="foundation.cospans%25E1%25B5%2589.html#2372" class="Function">swap-cospanᵉ</a> <a id="2385" class="Symbol">:</a>
  <a id="2389" class="Symbol">{</a><a id="2390" href="foundation.cospans%25E1%25B5%2589.html#2390" class="Bound">l1ᵉ</a> <a id="2394" href="foundation.cospans%25E1%25B5%2589.html#2394" class="Bound">l2ᵉ</a> <a id="2398" class="Symbol">:</a> <a id="2400" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2405" class="Symbol">}</a> <a id="2407" class="Symbol">{</a><a id="2408" href="foundation.cospans%25E1%25B5%2589.html#2408" class="Bound">lᵉ</a> <a id="2411" class="Symbol">:</a> <a id="2413" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2418" class="Symbol">}</a> <a id="2420" class="Symbol">{</a><a id="2421" href="foundation.cospans%25E1%25B5%2589.html#2421" class="Bound">Aᵉ</a> <a id="2424" class="Symbol">:</a> <a id="2426" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2430" href="foundation.cospans%25E1%25B5%2589.html#2390" class="Bound">l1ᵉ</a><a id="2433" class="Symbol">}</a> <a id="2435" class="Symbol">{</a><a id="2436" href="foundation.cospans%25E1%25B5%2589.html#2436" class="Bound">Bᵉ</a> <a id="2439" class="Symbol">:</a> <a id="2441" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2445" href="foundation.cospans%25E1%25B5%2589.html#2394" class="Bound">l2ᵉ</a><a id="2448" class="Symbol">}</a> <a id="2450" class="Symbol">→</a>
  <a id="2454" href="foundation.cospans%25E1%25B5%2589.html#1697" class="Function">cospanᵉ</a> <a id="2462" href="foundation.cospans%25E1%25B5%2589.html#2408" class="Bound">lᵉ</a> <a id="2465" href="foundation.cospans%25E1%25B5%2589.html#2421" class="Bound">Aᵉ</a> <a id="2468" href="foundation.cospans%25E1%25B5%2589.html#2436" class="Bound">Bᵉ</a> <a id="2471" class="Symbol">→</a> <a id="2473" href="foundation.cospans%25E1%25B5%2589.html#1697" class="Function">cospanᵉ</a> <a id="2481" href="foundation.cospans%25E1%25B5%2589.html#2408" class="Bound">lᵉ</a> <a id="2484" href="foundation.cospans%25E1%25B5%2589.html#2436" class="Bound">Bᵉ</a> <a id="2487" href="foundation.cospans%25E1%25B5%2589.html#2421" class="Bound">Aᵉ</a>
<a id="2490" href="foundation.cospans%25E1%25B5%2589.html#2372" class="Function">swap-cospanᵉ</a> <a id="2503" class="Symbol">(</a><a id="2504" href="foundation.cospans%25E1%25B5%2589.html#2504" class="Bound">Cᵉ</a> <a id="2507" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2510" href="foundation.cospans%25E1%25B5%2589.html#2510" class="Bound">fᵉ</a> <a id="2513" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2516" href="foundation.cospans%25E1%25B5%2589.html#2516" class="Bound">gᵉ</a><a id="2518" class="Symbol">)</a> <a id="2520" class="Symbol">=</a> <a id="2522" class="Symbol">(</a><a id="2523" href="foundation.cospans%25E1%25B5%2589.html#2504" class="Bound">Cᵉ</a> <a id="2526" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2529" href="foundation.cospans%25E1%25B5%2589.html#2516" class="Bound">gᵉ</a> <a id="2532" href="foundation.dependent-pair-types%25E1%25B5%2589.html#788" class="InductiveConstructor Operator">,ᵉ</a> <a id="2535" href="foundation.cospans%25E1%25B5%2589.html#2510" class="Bound">fᵉ</a><a id="2537" class="Symbol">)</a>
</pre>
## See also

- The formal dual of cospans is [spans](foundation.spans.md).
- [Pullbacks](foundation-core.pullbacks.md) are limits of
  [cospan diagrams](foundation.cospan-diagrams.md).

### Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}