# Double lifts of families of elements

<pre class="Agda"><a id="49" class="Keyword">module</a> <a id="56" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html" class="Module">orthogonal-factorization-systems.double-lifts-families-of-elements</a> <a id="123" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="179" class="Keyword">open</a> <a id="184" class="Keyword">import</a> <a id="191" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="219" class="Keyword">open</a> <a id="224" class="Keyword">import</a> <a id="231" href="orthogonal-factorization-systems.lifts-families-of-elements.html" class="Module">orthogonal-factorization-systems.lifts-families-of-elements</a>
</pre>
</details>

## Idea

Consider a family of elements `b : (i : I) → B i (a i)` over a family of
elements `a : (i : I) → A i` and consider a family of types

```text
  C : (i : I) (x : A i) → B i x → 𝒰.
```

Recall that `b` is also a
[dependent lift](orthogonal-factorization-systems.lifts-families-of-elements.md)
of the family of elements `a`. The type of
{{#concept "dependent double lifts" Disambiguation="family of elements" Agda=dependent-double-lift-family-of-elements}}
of `b` and `a` to `C` is defined to be the type

```text
  (i : I) → C i (a i) (b i).
```

Note that this is the type of double lifts in the sense that it simultaneously
lifts `a` and `b` to the type family `C`.

The definition of (ordinary) double lifts is somewhat simpler: Given a lift `b`
of `a : I → A` to a type family `B : A → 𝒰`, a
{{#concept "double lift" Disambiguation="families of elements" Agda=double-lift-family-of-elements}}
of `a` and `b` to a type family

```text
  C : (x : A) → B x → 𝒰
```

is a family of elements

```text
  (i : I) → C (a i) (b i).
```

Note that this is the type of double lifts in the sense that it simultaneously
lifts `a` and `b` to the type family `C`.

The type of double lifts plays a role in the
[universal property of the family of fibers of a map](foundation.universal-property-family-of-fibers-of-maps.md).

## Definitions

### Dependent double lifts of families of elements

<pre class="Agda"><a id="1705" class="Keyword">module</a> <a id="1712" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1712" class="Module">_</a>
  <a id="1716" class="Symbol">{</a><a id="1717" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1717" class="Bound">l1</a> <a id="1720" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1720" class="Bound">l2</a> <a id="1723" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1723" class="Bound">l3</a> <a id="1726" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1726" class="Bound">l4</a> <a id="1729" class="Symbol">:</a> <a id="1731" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1736" class="Symbol">}</a> <a id="1738" class="Symbol">{</a><a id="1739" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1739" class="Bound">I</a> <a id="1741" class="Symbol">:</a> <a id="1743" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1746" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1717" class="Bound">l1</a><a id="1748" class="Symbol">}</a> <a id="1750" class="Symbol">{</a><a id="1751" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1751" class="Bound">A</a> <a id="1753" class="Symbol">:</a> <a id="1755" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1739" class="Bound">I</a> <a id="1757" class="Symbol">→</a> <a id="1759" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1762" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1720" class="Bound">l2</a><a id="1764" class="Symbol">}</a> <a id="1766" class="Symbol">{</a><a id="1767" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1767" class="Bound">B</a> <a id="1769" class="Symbol">:</a> <a id="1771" class="Symbol">(</a><a id="1772" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1772" class="Bound">i</a> <a id="1774" class="Symbol">:</a> <a id="1776" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1739" class="Bound">I</a><a id="1777" class="Symbol">)</a> <a id="1779" class="Symbol">→</a> <a id="1781" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1751" class="Bound">A</a> <a id="1783" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1772" class="Bound">i</a> <a id="1785" class="Symbol">→</a> <a id="1787" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1790" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1723" class="Bound">l3</a><a id="1792" class="Symbol">}</a>
  <a id="1796" class="Symbol">(</a><a id="1797" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1797" class="Bound">C</a> <a id="1799" class="Symbol">:</a> <a id="1801" class="Symbol">(</a><a id="1802" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1802" class="Bound">i</a> <a id="1804" class="Symbol">:</a> <a id="1806" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1739" class="Bound">I</a><a id="1807" class="Symbol">)</a> <a id="1809" class="Symbol">(</a><a id="1810" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1810" class="Bound">x</a> <a id="1812" class="Symbol">:</a> <a id="1814" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1751" class="Bound">A</a> <a id="1816" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1802" class="Bound">i</a><a id="1817" class="Symbol">)</a> <a id="1819" class="Symbol">→</a> <a id="1821" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1767" class="Bound">B</a> <a id="1823" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1802" class="Bound">i</a> <a id="1825" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1810" class="Bound">x</a> <a id="1827" class="Symbol">→</a> <a id="1829" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1832" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1726" class="Bound">l4</a><a id="1834" class="Symbol">)</a>
  <a id="1838" class="Symbol">{</a><a id="1839" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1839" class="Bound">a</a> <a id="1841" class="Symbol">:</a> <a id="1843" class="Symbol">(</a><a id="1844" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1844" class="Bound">i</a> <a id="1846" class="Symbol">:</a> <a id="1848" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1739" class="Bound">I</a><a id="1849" class="Symbol">)</a> <a id="1851" class="Symbol">→</a> <a id="1853" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1751" class="Bound">A</a> <a id="1855" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1844" class="Bound">i</a><a id="1856" class="Symbol">}</a> <a id="1858" class="Symbol">(</a><a id="1859" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1859" class="Bound">b</a> <a id="1861" class="Symbol">:</a> <a id="1863" href="orthogonal-factorization-systems.lifts-families-of-elements.html#2686" class="Function">dependent-lift-family-of-elements</a> <a id="1897" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1767" class="Bound">B</a> <a id="1899" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1839" class="Bound">a</a><a id="1900" class="Symbol">)</a>
  <a id="1904" class="Keyword">where</a>

  <a id="1913" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1913" class="Function">dependent-double-lift-family-of-elements</a> <a id="1954" class="Symbol">:</a> <a id="1956" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1959" class="Symbol">(</a><a id="1960" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1717" class="Bound">l1</a> <a id="1963" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1965" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1726" class="Bound">l4</a><a id="1967" class="Symbol">)</a>
  <a id="1971" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1913" class="Function">dependent-double-lift-family-of-elements</a> <a id="2012" class="Symbol">=</a>
    <a id="2018" href="orthogonal-factorization-systems.lifts-families-of-elements.html#2686" class="Function">dependent-lift-family-of-elements</a> <a id="2052" class="Symbol">(λ</a> <a id="2055" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2055" class="Bound">i</a> <a id="2057" class="Symbol">→</a> <a id="2059" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1797" class="Bound">C</a> <a id="2061" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2055" class="Bound">i</a> <a id="2063" class="Symbol">(</a><a id="2064" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1839" class="Bound">a</a> <a id="2066" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2055" class="Bound">i</a><a id="2067" class="Symbol">))</a> <a id="2070" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#1859" class="Bound">b</a>
</pre>
### Double lifts of families of elements

<pre class="Agda"><a id="2127" class="Keyword">module</a> <a id="2134" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2134" class="Module">_</a>
  <a id="2138" class="Symbol">{</a><a id="2139" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2139" class="Bound">l1</a> <a id="2142" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2142" class="Bound">l2</a> <a id="2145" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2145" class="Bound">l3</a> <a id="2148" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2148" class="Bound">l4</a> <a id="2151" class="Symbol">:</a> <a id="2153" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2158" class="Symbol">}</a> <a id="2160" class="Symbol">{</a><a id="2161" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2161" class="Bound">I</a> <a id="2163" class="Symbol">:</a> <a id="2165" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2168" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2139" class="Bound">l1</a><a id="2170" class="Symbol">}</a> <a id="2172" class="Symbol">{</a><a id="2173" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2173" class="Bound">A</a> <a id="2175" class="Symbol">:</a> <a id="2177" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2180" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2142" class="Bound">l2</a><a id="2182" class="Symbol">}</a> <a id="2184" class="Symbol">{</a><a id="2185" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2185" class="Bound">B</a> <a id="2187" class="Symbol">:</a> <a id="2189" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2173" class="Bound">A</a> <a id="2191" class="Symbol">→</a> <a id="2193" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2196" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2145" class="Bound">l3</a><a id="2198" class="Symbol">}</a>
  <a id="2202" class="Symbol">(</a><a id="2203" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2203" class="Bound">C</a> <a id="2205" class="Symbol">:</a> <a id="2207" class="Symbol">(</a><a id="2208" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2208" class="Bound">x</a> <a id="2210" class="Symbol">:</a> <a id="2212" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2173" class="Bound">A</a><a id="2213" class="Symbol">)</a> <a id="2215" class="Symbol">→</a> <a id="2217" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2185" class="Bound">B</a> <a id="2219" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2208" class="Bound">x</a> <a id="2221" class="Symbol">→</a> <a id="2223" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2226" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2148" class="Bound">l4</a><a id="2228" class="Symbol">)</a>
  <a id="2232" class="Symbol">{</a><a id="2233" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2233" class="Bound">a</a> <a id="2235" class="Symbol">:</a> <a id="2237" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2161" class="Bound">I</a> <a id="2239" class="Symbol">→</a> <a id="2241" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2173" class="Bound">A</a><a id="2242" class="Symbol">}</a> <a id="2244" class="Symbol">(</a><a id="2245" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2245" class="Bound">b</a> <a id="2247" class="Symbol">:</a> <a id="2249" href="orthogonal-factorization-systems.lifts-families-of-elements.html#2934" class="Function">lift-family-of-elements</a> <a id="2273" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2185" class="Bound">B</a> <a id="2275" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2233" class="Bound">a</a><a id="2276" class="Symbol">)</a>
  <a id="2280" class="Keyword">where</a>

  <a id="2289" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2289" class="Function">double-lift-family-of-elements</a> <a id="2320" class="Symbol">:</a> <a id="2322" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2325" class="Symbol">(</a><a id="2326" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2139" class="Bound">l1</a> <a id="2329" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2331" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2148" class="Bound">l4</a><a id="2333" class="Symbol">)</a>
  <a id="2337" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2289" class="Function">double-lift-family-of-elements</a> <a id="2368" class="Symbol">=</a>
    <a id="2374" href="orthogonal-factorization-systems.lifts-families-of-elements.html#2686" class="Function">dependent-lift-family-of-elements</a> <a id="2408" class="Symbol">(λ</a> <a id="2411" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2411" class="Bound">i</a> <a id="2413" class="Symbol">→</a> <a id="2415" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2203" class="Bound">C</a> <a id="2417" class="Symbol">(</a><a id="2418" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2233" class="Bound">a</a> <a id="2420" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2411" class="Bound">i</a><a id="2421" class="Symbol">))</a> <a id="2424" href="orthogonal-factorization-systems.double-lifts-families-of-elements.html#2245" class="Bound">b</a>
</pre>
## See also

- [Lifts of families of elements](orthogonal-factorization-systems.lifts-families-of-elements.md)
- [Lifts of maps](orthogonal-factorization-systems.lifts-of-maps.md)
- [The universal property of the family of fibers of a map](foundation.universal-property-family-of-fibers-of-maps.md)
