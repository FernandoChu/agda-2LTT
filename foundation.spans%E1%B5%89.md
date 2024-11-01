# Spans of types

<pre class="Agda"><a id="27" class="Keyword">module</a> <a id="34" href="foundation.spans%25E1%25B5%2589.html" class="Module">foundation.spansᵉ</a> <a id="52" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="108" class="Keyword">open</a> <a id="113" class="Keyword">import</a> <a id="120" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="153" class="Keyword">open</a> <a id="158" class="Keyword">import</a> <a id="165" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="194" class="Keyword">open</a> <a id="199" class="Keyword">import</a> <a id="206" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html" class="Module">foundation-core.cartesian-product-typesᵉ</a>
<a id="247" class="Keyword">open</a> <a id="252" class="Keyword">import</a> <a id="259" href="foundation-core.function-types%25E1%25B5%2589.html" class="Module">foundation-core.function-typesᵉ</a>
</pre>
</details>

## Idea

A {{#concept "binary span" Agda=span}} from `A` to `B` consists of a
{{#concept "spanning type" Disambiguation="binary span" Agda=spanning-type-span}}
`S` and a [pair](foundation.dependent-pair-types.md) of functions `f : S → A`
and `g : S → B`. The types `A` and `B` in the specification of a binary span are
also referred to as the {{#concept "domain" Disambiguation="binary span"}} and
{{#concept "codomain" Disambiguation="binary span"}} of the span, respectively.

In [`foundation.binary-type-duality`](foundation.binary-type-duality.md) we show
that [binary relations](foundation.binary-relations.md) are equivalently
described as spans of types.

We disambiguate between spans and [span diagrams](foundation.span-diagrams.md).
We consider spans from `A` to `B` to be _morphisms_ from `A` to `B` in the
category of types and spans between them, whereas we consider span diagrams to
be _objects_ in the category of diagrams of types of the form
`* <---- * ----> *`. Conceptually there is a subtle, but important distinction
between spans and span diagrams. As mentioned previously, a span from `A` to `B`
is equivalently described as a binary relation from `A` to `B`. On the other
hand, span diagrams are more suitable for functorial operations that take
"spans" as input, but for which the functorial action takes a natural
transformation, i.e., a morphism of span diagrams, as input. Examples of this
kind include [pushouts](synthetic-homotopy-theory.pushouts.md).

## Definitions

### (Binary) spans

<pre class="Agda"><a id="spanᵉ"></a><a id="1835" href="foundation.spans%25E1%25B5%2589.html#1835" class="Function">spanᵉ</a> <a id="1841" class="Symbol">:</a>
  <a id="1845" class="Symbol">{</a><a id="1846" href="foundation.spans%25E1%25B5%2589.html#1846" class="Bound">l1ᵉ</a> <a id="1850" href="foundation.spans%25E1%25B5%2589.html#1850" class="Bound">l2ᵉ</a> <a id="1854" class="Symbol">:</a> <a id="1856" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1861" class="Symbol">}</a> <a id="1863" class="Symbol">(</a><a id="1864" href="foundation.spans%25E1%25B5%2589.html#1864" class="Bound">lᵉ</a> <a id="1867" class="Symbol">:</a> <a id="1869" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1874" class="Symbol">)</a> <a id="1876" class="Symbol">(</a><a id="1877" href="foundation.spans%25E1%25B5%2589.html#1877" class="Bound">Aᵉ</a> <a id="1880" class="Symbol">:</a> <a id="1882" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1886" href="foundation.spans%25E1%25B5%2589.html#1846" class="Bound">l1ᵉ</a><a id="1889" class="Symbol">)</a> <a id="1891" class="Symbol">(</a><a id="1892" href="foundation.spans%25E1%25B5%2589.html#1892" class="Bound">Bᵉ</a> <a id="1895" class="Symbol">:</a> <a id="1897" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1901" href="foundation.spans%25E1%25B5%2589.html#1850" class="Bound">l2ᵉ</a><a id="1904" class="Symbol">)</a> <a id="1906" class="Symbol">→</a> <a id="1908" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1912" class="Symbol">(</a><a id="1913" href="foundation.spans%25E1%25B5%2589.html#1846" class="Bound">l1ᵉ</a> <a id="1917" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1919" href="foundation.spans%25E1%25B5%2589.html#1850" class="Bound">l2ᵉ</a> <a id="1923" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1925" href="Agda.Primitive.html#931" class="Primitive">lsuc</a> <a id="1930" href="foundation.spans%25E1%25B5%2589.html#1864" class="Bound">lᵉ</a><a id="1932" class="Symbol">)</a>
<a id="1934" href="foundation.spans%25E1%25B5%2589.html#1835" class="Function">spanᵉ</a> <a id="1940" href="foundation.spans%25E1%25B5%2589.html#1940" class="Bound">lᵉ</a> <a id="1943" href="foundation.spans%25E1%25B5%2589.html#1943" class="Bound">Aᵉ</a> <a id="1946" href="foundation.spans%25E1%25B5%2589.html#1946" class="Bound">Bᵉ</a> <a id="1949" class="Symbol">=</a> <a id="1951" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="1954" class="Symbol">(</a><a id="1955" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="1959" href="foundation.spans%25E1%25B5%2589.html#1940" class="Bound">lᵉ</a><a id="1961" class="Symbol">)</a> <a id="1963" class="Symbol">(λ</a> <a id="1966" href="foundation.spans%25E1%25B5%2589.html#1966" class="Bound">Xᵉ</a> <a id="1969" class="Symbol">→</a> <a id="1971" class="Symbol">(</a><a id="1972" href="foundation.spans%25E1%25B5%2589.html#1966" class="Bound">Xᵉ</a> <a id="1975" class="Symbol">→</a> <a id="1977" href="foundation.spans%25E1%25B5%2589.html#1943" class="Bound">Aᵉ</a><a id="1979" class="Symbol">)</a> <a id="1981" href="foundation-core.cartesian-product-types%25E1%25B5%2589.html#623" class="Function Operator">×ᵉ</a> <a id="1984" class="Symbol">(</a><a id="1985" href="foundation.spans%25E1%25B5%2589.html#1966" class="Bound">Xᵉ</a> <a id="1988" class="Symbol">→</a> <a id="1990" href="foundation.spans%25E1%25B5%2589.html#1946" class="Bound">Bᵉ</a><a id="1992" class="Symbol">))</a>

<a id="1996" class="Keyword">module</a> <a id="2003" href="foundation.spans%25E1%25B5%2589.html#2003" class="Module">_</a>
  <a id="2007" class="Symbol">{</a><a id="2008" href="foundation.spans%25E1%25B5%2589.html#2008" class="Bound">l1ᵉ</a> <a id="2012" href="foundation.spans%25E1%25B5%2589.html#2012" class="Bound">l2ᵉ</a> <a id="2016" href="foundation.spans%25E1%25B5%2589.html#2016" class="Bound">l3ᵉ</a> <a id="2020" class="Symbol">:</a> <a id="2022" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2027" class="Symbol">}</a> <a id="2029" class="Symbol">{</a><a id="2030" href="foundation.spans%25E1%25B5%2589.html#2030" class="Bound">Aᵉ</a> <a id="2033" class="Symbol">:</a> <a id="2035" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2039" href="foundation.spans%25E1%25B5%2589.html#2008" class="Bound">l1ᵉ</a><a id="2042" class="Symbol">}</a> <a id="2044" class="Symbol">{</a><a id="2045" href="foundation.spans%25E1%25B5%2589.html#2045" class="Bound">Bᵉ</a> <a id="2048" class="Symbol">:</a> <a id="2050" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2054" href="foundation.spans%25E1%25B5%2589.html#2012" class="Bound">l2ᵉ</a><a id="2057" class="Symbol">}</a>
  <a id="2061" class="Symbol">(</a><a id="2062" href="foundation.spans%25E1%25B5%2589.html#2062" class="Bound">cᵉ</a> <a id="2065" class="Symbol">:</a> <a id="2067" href="foundation.spans%25E1%25B5%2589.html#1835" class="Function">spanᵉ</a> <a id="2073" href="foundation.spans%25E1%25B5%2589.html#2016" class="Bound">l3ᵉ</a> <a id="2077" href="foundation.spans%25E1%25B5%2589.html#2030" class="Bound">Aᵉ</a> <a id="2080" href="foundation.spans%25E1%25B5%2589.html#2045" class="Bound">Bᵉ</a><a id="2082" class="Symbol">)</a>
  <a id="2086" class="Keyword">where</a>

  <a id="2095" href="foundation.spans%25E1%25B5%2589.html#2095" class="Function">spanning-type-spanᵉ</a> <a id="2115" class="Symbol">:</a> <a id="2117" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2121" href="foundation.spans%25E1%25B5%2589.html#2016" class="Bound">l3ᵉ</a>
  <a id="2127" href="foundation.spans%25E1%25B5%2589.html#2095" class="Function">spanning-type-spanᵉ</a> <a id="2147" class="Symbol">=</a> <a id="2149" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="2154" href="foundation.spans%25E1%25B5%2589.html#2062" class="Bound">cᵉ</a>

  <a id="2160" href="foundation.spans%25E1%25B5%2589.html#2160" class="Function">left-map-spanᵉ</a> <a id="2175" class="Symbol">:</a> <a id="2177" href="foundation.spans%25E1%25B5%2589.html#2095" class="Function">spanning-type-spanᵉ</a> <a id="2197" class="Symbol">→</a> <a id="2199" href="foundation.spans%25E1%25B5%2589.html#2030" class="Bound">Aᵉ</a>
  <a id="2204" href="foundation.spans%25E1%25B5%2589.html#2160" class="Function">left-map-spanᵉ</a> <a id="2219" class="Symbol">=</a> <a id="2221" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="2226" class="Symbol">(</a><a id="2227" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="2232" href="foundation.spans%25E1%25B5%2589.html#2062" class="Bound">cᵉ</a><a id="2234" class="Symbol">)</a>

  <a id="2239" href="foundation.spans%25E1%25B5%2589.html#2239" class="Function">right-map-spanᵉ</a> <a id="2255" class="Symbol">:</a> <a id="2257" href="foundation.spans%25E1%25B5%2589.html#2095" class="Function">spanning-type-spanᵉ</a> <a id="2277" class="Symbol">→</a> <a id="2279" href="foundation.spans%25E1%25B5%2589.html#2045" class="Bound">Bᵉ</a>
  <a id="2284" href="foundation.spans%25E1%25B5%2589.html#2239" class="Function">right-map-spanᵉ</a> <a id="2300" class="Symbol">=</a> <a id="2302" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="2307" class="Symbol">(</a><a id="2308" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="2313" href="foundation.spans%25E1%25B5%2589.html#2062" class="Bound">cᵉ</a><a id="2315" class="Symbol">)</a>
</pre>
### Identity spans

<pre class="Agda"><a id="2350" class="Keyword">module</a> <a id="2357" href="foundation.spans%25E1%25B5%2589.html#2357" class="Module">_</a>
  <a id="2361" class="Symbol">{</a><a id="2362" href="foundation.spans%25E1%25B5%2589.html#2362" class="Bound">l1ᵉ</a> <a id="2366" class="Symbol">:</a> <a id="2368" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2373" class="Symbol">}</a> <a id="2375" class="Symbol">{</a><a id="2376" href="foundation.spans%25E1%25B5%2589.html#2376" class="Bound">Xᵉ</a> <a id="2379" class="Symbol">:</a> <a id="2381" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2385" href="foundation.spans%25E1%25B5%2589.html#2362" class="Bound">l1ᵉ</a><a id="2388" class="Symbol">}</a>
  <a id="2392" class="Keyword">where</a>

  <a id="2401" href="foundation.spans%25E1%25B5%2589.html#2401" class="Function">id-spanᵉ</a> <a id="2410" class="Symbol">:</a> <a id="2412" href="foundation.spans%25E1%25B5%2589.html#1835" class="Function">spanᵉ</a> <a id="2418" href="foundation.spans%25E1%25B5%2589.html#2362" class="Bound">l1ᵉ</a> <a id="2422" href="foundation.spans%25E1%25B5%2589.html#2376" class="Bound">Xᵉ</a> <a id="2425" href="foundation.spans%25E1%25B5%2589.html#2376" class="Bound">Xᵉ</a>
  <a id="2430" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="2435" href="foundation.spans%25E1%25B5%2589.html#2401" class="Function">id-spanᵉ</a> <a id="2444" class="Symbol">=</a> <a id="2446" href="foundation.spans%25E1%25B5%2589.html#2376" class="Bound">Xᵉ</a>
  <a id="2451" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="2456" class="Symbol">(</a><a id="2457" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="2462" href="foundation.spans%25E1%25B5%2589.html#2401" class="Function">id-spanᵉ</a><a id="2470" class="Symbol">)</a> <a id="2472" class="Symbol">=</a> <a id="2474" href="foundation-core.function-types%25E1%25B5%2589.html#309" class="Function">idᵉ</a>
  <a id="2480" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="2485" class="Symbol">(</a><a id="2486" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="2491" href="foundation.spans%25E1%25B5%2589.html#2401" class="Function">id-spanᵉ</a><a id="2499" class="Symbol">)</a> <a id="2501" class="Symbol">=</a> <a id="2503" href="foundation-core.function-types%25E1%25B5%2589.html#309" class="Function">idᵉ</a>
</pre>
## See also

- [Binary type duality](foundation.binary-type-duality.md)
- [Cospans](foundation.cospans.md)
- [Span diagrams](foundation.span-diagrams.md)
- [Spans of families of types](foundation.spans-families-of-types.md)
- [Spans of pointed types](structured-types.pointed-spans.md)