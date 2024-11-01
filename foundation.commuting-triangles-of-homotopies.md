# Commuting triangles of homotopies

<pre class="Agda"><a id="46" class="Keyword">module</a> <a id="53" href="foundation.commuting-triangles-of-homotopies.html" class="Module">foundation.commuting-triangles-of-homotopies</a> <a id="98" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="154" class="Keyword">open</a> <a id="159" class="Keyword">import</a> <a id="166" href="foundation.commuting-triangles-of-identifications.html" class="Module">foundation.commuting-triangles-of-identifications</a>
<a id="216" class="Keyword">open</a> <a id="221" class="Keyword">import</a> <a id="228" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="255" class="Keyword">open</a> <a id="260" class="Keyword">import</a> <a id="267" href="foundation.whiskering-homotopies-composition.html" class="Module">foundation.whiskering-homotopies-composition</a>

<a id="313" class="Keyword">open</a> <a id="318" class="Keyword">import</a> <a id="325" href="foundation-core.function-types.html" class="Module">foundation-core.function-types</a>
<a id="356" class="Keyword">open</a> <a id="361" class="Keyword">import</a> <a id="368" href="foundation-core.homotopies.html" class="Module">foundation-core.homotopies</a>
</pre>
</details>

## Idea

A triangle of [homotopies](foundation-core.homotopies.md) of dependent functions

```text
      top
    f ----> g
     \     /
 left \   / right
       ∨ ∨
        h
```

is said to
{{#concept "commute" Disambiguation="triangle of homotopies" Agda=coherence-triangle-homotopies}}
if there is a homotopy `left ~ top ∙h right`.

## Definitions

### Coherences of commuting triangles of homotopies

<pre class="Agda"><a id="825" class="Keyword">module</a> <a id="832" href="foundation.commuting-triangles-of-homotopies.html#832" class="Module">_</a>
  <a id="836" class="Symbol">{</a><a id="837" href="foundation.commuting-triangles-of-homotopies.html#837" class="Bound">l1</a> <a id="840" href="foundation.commuting-triangles-of-homotopies.html#840" class="Bound">l2</a> <a id="843" class="Symbol">:</a> <a id="845" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="850" class="Symbol">}</a> <a id="852" class="Symbol">{</a><a id="853" href="foundation.commuting-triangles-of-homotopies.html#853" class="Bound">A</a> <a id="855" class="Symbol">:</a> <a id="857" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="860" href="foundation.commuting-triangles-of-homotopies.html#837" class="Bound">l1</a><a id="862" class="Symbol">}</a> <a id="864" class="Symbol">{</a><a id="865" href="foundation.commuting-triangles-of-homotopies.html#865" class="Bound">B</a> <a id="867" class="Symbol">:</a> <a id="869" href="foundation.commuting-triangles-of-homotopies.html#853" class="Bound">A</a> <a id="871" class="Symbol">→</a> <a id="873" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="876" href="foundation.commuting-triangles-of-homotopies.html#840" class="Bound">l2</a><a id="878" class="Symbol">}</a>
  <a id="882" class="Symbol">{</a><a id="883" href="foundation.commuting-triangles-of-homotopies.html#883" class="Bound">f</a> <a id="885" href="foundation.commuting-triangles-of-homotopies.html#885" class="Bound">g</a> <a id="887" href="foundation.commuting-triangles-of-homotopies.html#887" class="Bound">h</a> <a id="889" class="Symbol">:</a> <a id="891" class="Symbol">(</a><a id="892" href="foundation.commuting-triangles-of-homotopies.html#892" class="Bound">x</a> <a id="894" class="Symbol">:</a> <a id="896" href="foundation.commuting-triangles-of-homotopies.html#853" class="Bound">A</a><a id="897" class="Symbol">)</a> <a id="899" class="Symbol">→</a> <a id="901" href="foundation.commuting-triangles-of-homotopies.html#865" class="Bound">B</a> <a id="903" href="foundation.commuting-triangles-of-homotopies.html#892" class="Bound">x</a><a id="904" class="Symbol">}</a>
  <a id="908" class="Keyword">where</a>

  <a id="917" href="foundation.commuting-triangles-of-homotopies.html#917" class="Function">coherence-triangle-homotopies</a> <a id="947" class="Symbol">:</a>
    <a id="953" class="Symbol">(</a><a id="954" href="foundation.commuting-triangles-of-homotopies.html#954" class="Bound">left</a> <a id="959" class="Symbol">:</a> <a id="961" href="foundation.commuting-triangles-of-homotopies.html#883" class="Bound">f</a> <a id="963" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="965" href="foundation.commuting-triangles-of-homotopies.html#887" class="Bound">h</a><a id="966" class="Symbol">)</a> <a id="968" class="Symbol">(</a><a id="969" href="foundation.commuting-triangles-of-homotopies.html#969" class="Bound">right</a> <a id="975" class="Symbol">:</a> <a id="977" href="foundation.commuting-triangles-of-homotopies.html#885" class="Bound">g</a> <a id="979" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="981" href="foundation.commuting-triangles-of-homotopies.html#887" class="Bound">h</a><a id="982" class="Symbol">)</a> <a id="984" class="Symbol">(</a><a id="985" href="foundation.commuting-triangles-of-homotopies.html#985" class="Bound">top</a> <a id="989" class="Symbol">:</a> <a id="991" href="foundation.commuting-triangles-of-homotopies.html#883" class="Bound">f</a> <a id="993" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="995" href="foundation.commuting-triangles-of-homotopies.html#885" class="Bound">g</a><a id="996" class="Symbol">)</a> <a id="998" class="Symbol">→</a> <a id="1000" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1003" class="Symbol">(</a><a id="1004" href="foundation.commuting-triangles-of-homotopies.html#837" class="Bound">l1</a> <a id="1007" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1009" href="foundation.commuting-triangles-of-homotopies.html#840" class="Bound">l2</a><a id="1011" class="Symbol">)</a>
  <a id="1015" href="foundation.commuting-triangles-of-homotopies.html#917" class="Function">coherence-triangle-homotopies</a> <a id="1045" href="foundation.commuting-triangles-of-homotopies.html#1045" class="Bound">left</a> <a id="1050" href="foundation.commuting-triangles-of-homotopies.html#1050" class="Bound">right</a> <a id="1056" href="foundation.commuting-triangles-of-homotopies.html#1056" class="Bound">top</a> <a id="1060" class="Symbol">=</a> <a id="1062" href="foundation.commuting-triangles-of-homotopies.html#1045" class="Bound">left</a> <a id="1067" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1069" href="foundation.commuting-triangles-of-homotopies.html#1056" class="Bound">top</a> <a id="1073" href="foundation-core.homotopies.html#3099" class="Function Operator">∙h</a> <a id="1076" href="foundation.commuting-triangles-of-homotopies.html#1050" class="Bound">right</a>

  <a id="1085" href="foundation.commuting-triangles-of-homotopies.html#1085" class="Function">coherence-triangle-homotopies&#39;</a> <a id="1116" class="Symbol">:</a>
    <a id="1122" class="Symbol">(</a><a id="1123" href="foundation.commuting-triangles-of-homotopies.html#1123" class="Bound">left</a> <a id="1128" class="Symbol">:</a> <a id="1130" href="foundation.commuting-triangles-of-homotopies.html#883" class="Bound">f</a> <a id="1132" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1134" href="foundation.commuting-triangles-of-homotopies.html#887" class="Bound">h</a><a id="1135" class="Symbol">)</a> <a id="1137" class="Symbol">(</a><a id="1138" href="foundation.commuting-triangles-of-homotopies.html#1138" class="Bound">right</a> <a id="1144" class="Symbol">:</a> <a id="1146" href="foundation.commuting-triangles-of-homotopies.html#885" class="Bound">g</a> <a id="1148" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1150" href="foundation.commuting-triangles-of-homotopies.html#887" class="Bound">h</a><a id="1151" class="Symbol">)</a> <a id="1153" class="Symbol">(</a><a id="1154" href="foundation.commuting-triangles-of-homotopies.html#1154" class="Bound">top</a> <a id="1158" class="Symbol">:</a> <a id="1160" href="foundation.commuting-triangles-of-homotopies.html#883" class="Bound">f</a> <a id="1162" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1164" href="foundation.commuting-triangles-of-homotopies.html#885" class="Bound">g</a><a id="1165" class="Symbol">)</a> <a id="1167" class="Symbol">→</a> <a id="1169" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1172" class="Symbol">(</a><a id="1173" href="foundation.commuting-triangles-of-homotopies.html#837" class="Bound">l1</a> <a id="1176" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="1178" href="foundation.commuting-triangles-of-homotopies.html#840" class="Bound">l2</a><a id="1180" class="Symbol">)</a>
  <a id="1184" href="foundation.commuting-triangles-of-homotopies.html#1085" class="Function">coherence-triangle-homotopies&#39;</a> <a id="1215" href="foundation.commuting-triangles-of-homotopies.html#1215" class="Bound">left</a> <a id="1220" href="foundation.commuting-triangles-of-homotopies.html#1220" class="Bound">right</a> <a id="1226" href="foundation.commuting-triangles-of-homotopies.html#1226" class="Bound">top</a> <a id="1230" class="Symbol">=</a> <a id="1232" href="foundation.commuting-triangles-of-homotopies.html#1226" class="Bound">top</a> <a id="1236" href="foundation-core.homotopies.html#3099" class="Function Operator">∙h</a> <a id="1239" href="foundation.commuting-triangles-of-homotopies.html#1220" class="Bound">right</a> <a id="1245" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1247" href="foundation.commuting-triangles-of-homotopies.html#1215" class="Bound">left</a>
</pre>
## Properties

### Left whiskering commuting triangles of homotopies with respect to concatenation of homotopies

Consider a commuting triangle of homotopies

```text
        top
     f ----> g
      \     /
  left \   / right
        ∨ ∨
         h
```

where `f g h : (x : A) → B x`, and consider a homotopy `H : i ~ f` for a fourth
dependent function `i : (x : A) → B x`. Then the triangle of homotopies

```text
           H ∙h top
         i --------> g
           \       /
  H ∙h left \     / right
             \   /
              ∨ ∨
               h
```

commutes.

<pre class="Agda"><a id="1841" class="Keyword">module</a> <a id="1848" href="foundation.commuting-triangles-of-homotopies.html#1848" class="Module">_</a>
  <a id="1852" class="Symbol">{</a><a id="1853" href="foundation.commuting-triangles-of-homotopies.html#1853" class="Bound">l1</a> <a id="1856" href="foundation.commuting-triangles-of-homotopies.html#1856" class="Bound">l2</a> <a id="1859" class="Symbol">:</a> <a id="1861" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1866" class="Symbol">}</a> <a id="1868" class="Symbol">{</a><a id="1869" href="foundation.commuting-triangles-of-homotopies.html#1869" class="Bound">A</a> <a id="1871" class="Symbol">:</a> <a id="1873" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1876" href="foundation.commuting-triangles-of-homotopies.html#1853" class="Bound">l1</a><a id="1878" class="Symbol">}</a> <a id="1880" class="Symbol">{</a><a id="1881" href="foundation.commuting-triangles-of-homotopies.html#1881" class="Bound">B</a> <a id="1883" class="Symbol">:</a> <a id="1885" href="foundation.commuting-triangles-of-homotopies.html#1869" class="Bound">A</a> <a id="1887" class="Symbol">→</a> <a id="1889" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1892" href="foundation.commuting-triangles-of-homotopies.html#1856" class="Bound">l2</a><a id="1894" class="Symbol">}</a>
  <a id="1898" class="Symbol">{</a><a id="1899" href="foundation.commuting-triangles-of-homotopies.html#1899" class="Bound">f</a> <a id="1901" href="foundation.commuting-triangles-of-homotopies.html#1901" class="Bound">g</a> <a id="1903" href="foundation.commuting-triangles-of-homotopies.html#1903" class="Bound">h</a> <a id="1905" href="foundation.commuting-triangles-of-homotopies.html#1905" class="Bound">i</a> <a id="1907" class="Symbol">:</a> <a id="1909" class="Symbol">(</a><a id="1910" href="foundation.commuting-triangles-of-homotopies.html#1910" class="Bound">x</a> <a id="1912" class="Symbol">:</a> <a id="1914" href="foundation.commuting-triangles-of-homotopies.html#1869" class="Bound">A</a><a id="1915" class="Symbol">)</a> <a id="1917" class="Symbol">→</a> <a id="1919" href="foundation.commuting-triangles-of-homotopies.html#1881" class="Bound">B</a> <a id="1921" href="foundation.commuting-triangles-of-homotopies.html#1910" class="Bound">x</a><a id="1922" class="Symbol">}</a> <a id="1924" class="Symbol">(</a><a id="1925" href="foundation.commuting-triangles-of-homotopies.html#1925" class="Bound">H</a> <a id="1927" class="Symbol">:</a> <a id="1929" href="foundation.commuting-triangles-of-homotopies.html#1905" class="Bound">i</a> <a id="1931" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1933" href="foundation.commuting-triangles-of-homotopies.html#1899" class="Bound">f</a><a id="1934" class="Symbol">)</a>
  <a id="1938" class="Symbol">(</a><a id="1939" href="foundation.commuting-triangles-of-homotopies.html#1939" class="Bound">left</a> <a id="1944" class="Symbol">:</a> <a id="1946" href="foundation.commuting-triangles-of-homotopies.html#1899" class="Bound">f</a> <a id="1948" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1950" href="foundation.commuting-triangles-of-homotopies.html#1903" class="Bound">h</a><a id="1951" class="Symbol">)</a> <a id="1953" class="Symbol">(</a><a id="1954" href="foundation.commuting-triangles-of-homotopies.html#1954" class="Bound">right</a> <a id="1960" class="Symbol">:</a> <a id="1962" href="foundation.commuting-triangles-of-homotopies.html#1901" class="Bound">g</a> <a id="1964" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1966" href="foundation.commuting-triangles-of-homotopies.html#1903" class="Bound">h</a><a id="1967" class="Symbol">)</a> <a id="1969" class="Symbol">(</a><a id="1970" href="foundation.commuting-triangles-of-homotopies.html#1970" class="Bound">top</a> <a id="1974" class="Symbol">:</a> <a id="1976" href="foundation.commuting-triangles-of-homotopies.html#1899" class="Bound">f</a> <a id="1978" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="1980" href="foundation.commuting-triangles-of-homotopies.html#1901" class="Bound">g</a><a id="1981" class="Symbol">)</a>
  <a id="1985" class="Keyword">where</a>

  <a id="1994" href="foundation.commuting-triangles-of-homotopies.html#1994" class="Function">left-whisker-concat-coherence-triangle-homotopies</a> <a id="2044" class="Symbol">:</a>
    <a id="2050" class="Symbol">(</a><a id="2051" href="foundation.commuting-triangles-of-homotopies.html#2051" class="Bound">T</a> <a id="2053" class="Symbol">:</a> <a id="2055" href="foundation.commuting-triangles-of-homotopies.html#917" class="Function">coherence-triangle-homotopies</a> <a id="2085" href="foundation.commuting-triangles-of-homotopies.html#1939" class="Bound">left</a> <a id="2090" href="foundation.commuting-triangles-of-homotopies.html#1954" class="Bound">right</a> <a id="2096" href="foundation.commuting-triangles-of-homotopies.html#1970" class="Bound">top</a><a id="2099" class="Symbol">)</a> <a id="2101" class="Symbol">→</a>
    <a id="2107" href="foundation.commuting-triangles-of-homotopies.html#917" class="Function">coherence-triangle-homotopies</a> <a id="2137" class="Symbol">(</a><a id="2138" href="foundation.commuting-triangles-of-homotopies.html#1925" class="Bound">H</a> <a id="2140" href="foundation-core.homotopies.html#3099" class="Function Operator">∙h</a> <a id="2143" href="foundation.commuting-triangles-of-homotopies.html#1939" class="Bound">left</a><a id="2147" class="Symbol">)</a> <a id="2149" href="foundation.commuting-triangles-of-homotopies.html#1954" class="Bound">right</a> <a id="2155" class="Symbol">(</a><a id="2156" href="foundation.commuting-triangles-of-homotopies.html#1925" class="Bound">H</a> <a id="2158" href="foundation-core.homotopies.html#3099" class="Function Operator">∙h</a> <a id="2161" href="foundation.commuting-triangles-of-homotopies.html#1970" class="Bound">top</a><a id="2164" class="Symbol">)</a>
  <a id="2168" href="foundation.commuting-triangles-of-homotopies.html#1994" class="Function">left-whisker-concat-coherence-triangle-homotopies</a> <a id="2218" href="foundation.commuting-triangles-of-homotopies.html#2218" class="Bound">T</a> <a id="2220" href="foundation.commuting-triangles-of-homotopies.html#2220" class="Bound">x</a> <a id="2222" class="Symbol">=</a>
    <a id="2228" href="foundation.commuting-triangles-of-identifications.html#4530" class="Function">left-whisker-concat-coherence-triangle-identifications</a>
      <a id="2289" class="Symbol">(</a> <a id="2291" href="foundation.commuting-triangles-of-homotopies.html#1925" class="Bound">H</a> <a id="2293" href="foundation.commuting-triangles-of-homotopies.html#2220" class="Bound">x</a><a id="2294" class="Symbol">)</a>
      <a id="2302" class="Symbol">(</a> <a id="2304" href="foundation.commuting-triangles-of-homotopies.html#1939" class="Bound">left</a> <a id="2309" href="foundation.commuting-triangles-of-homotopies.html#2220" class="Bound">x</a><a id="2310" class="Symbol">)</a>
      <a id="2318" class="Symbol">(</a> <a id="2320" href="foundation.commuting-triangles-of-homotopies.html#1954" class="Bound">right</a> <a id="2326" href="foundation.commuting-triangles-of-homotopies.html#2220" class="Bound">x</a><a id="2327" class="Symbol">)</a>
      <a id="2335" class="Symbol">(</a> <a id="2337" href="foundation.commuting-triangles-of-homotopies.html#1970" class="Bound">top</a> <a id="2341" href="foundation.commuting-triangles-of-homotopies.html#2220" class="Bound">x</a><a id="2342" class="Symbol">)</a>
      <a id="2350" class="Symbol">(</a> <a id="2352" href="foundation.commuting-triangles-of-homotopies.html#2218" class="Bound">T</a> <a id="2354" href="foundation.commuting-triangles-of-homotopies.html#2220" class="Bound">x</a><a id="2355" class="Symbol">)</a>
</pre>
### Right whiskering triangles of homotopies with respect to concatenation of homotopies

Consider a commuting triangle of homotopies

```text
        top
     f ----> g
      \     /
  left \   / right
        ∨ ∨
         h
```

where `f g h : (x : A) → B x`, and consider a homotopy `H : h ~ i` for a fourth
dependent function `i : (x : A) → B x`. Then the triangle of homotopies

```text
              top
         f --------> g
           \       /
  left ∙h H \     / right ∙h H
             \   /
              ∨ ∨
               i
```

commutes.

<pre class="Agda"><a id="2925" class="Keyword">module</a> <a id="2932" href="foundation.commuting-triangles-of-homotopies.html#2932" class="Module">_</a>
  <a id="2936" class="Symbol">{</a><a id="2937" href="foundation.commuting-triangles-of-homotopies.html#2937" class="Bound">l1</a> <a id="2940" href="foundation.commuting-triangles-of-homotopies.html#2940" class="Bound">l2</a> <a id="2943" class="Symbol">:</a> <a id="2945" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2950" class="Symbol">}</a> <a id="2952" class="Symbol">{</a><a id="2953" href="foundation.commuting-triangles-of-homotopies.html#2953" class="Bound">A</a> <a id="2955" class="Symbol">:</a> <a id="2957" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2960" href="foundation.commuting-triangles-of-homotopies.html#2937" class="Bound">l1</a><a id="2962" class="Symbol">}</a> <a id="2964" class="Symbol">{</a><a id="2965" href="foundation.commuting-triangles-of-homotopies.html#2965" class="Bound">B</a> <a id="2967" class="Symbol">:</a> <a id="2969" href="foundation.commuting-triangles-of-homotopies.html#2953" class="Bound">A</a> <a id="2971" class="Symbol">→</a> <a id="2973" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="2976" href="foundation.commuting-triangles-of-homotopies.html#2940" class="Bound">l2</a><a id="2978" class="Symbol">}</a>
  <a id="2982" class="Symbol">{</a><a id="2983" href="foundation.commuting-triangles-of-homotopies.html#2983" class="Bound">f</a> <a id="2985" href="foundation.commuting-triangles-of-homotopies.html#2985" class="Bound">g</a> <a id="2987" href="foundation.commuting-triangles-of-homotopies.html#2987" class="Bound">h</a> <a id="2989" class="Symbol">:</a> <a id="2991" class="Symbol">(</a><a id="2992" href="foundation.commuting-triangles-of-homotopies.html#2992" class="Bound">x</a> <a id="2994" class="Symbol">:</a> <a id="2996" href="foundation.commuting-triangles-of-homotopies.html#2953" class="Bound">A</a><a id="2997" class="Symbol">)</a> <a id="2999" class="Symbol">→</a> <a id="3001" href="foundation.commuting-triangles-of-homotopies.html#2965" class="Bound">B</a> <a id="3003" href="foundation.commuting-triangles-of-homotopies.html#2992" class="Bound">x</a><a id="3004" class="Symbol">}</a>
  <a id="3008" class="Symbol">(</a><a id="3009" href="foundation.commuting-triangles-of-homotopies.html#3009" class="Bound">left</a> <a id="3014" class="Symbol">:</a> <a id="3016" href="foundation.commuting-triangles-of-homotopies.html#2983" class="Bound">f</a> <a id="3018" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="3020" href="foundation.commuting-triangles-of-homotopies.html#2987" class="Bound">h</a><a id="3021" class="Symbol">)</a> <a id="3023" class="Symbol">(</a><a id="3024" href="foundation.commuting-triangles-of-homotopies.html#3024" class="Bound">right</a> <a id="3030" class="Symbol">:</a> <a id="3032" href="foundation.commuting-triangles-of-homotopies.html#2985" class="Bound">g</a> <a id="3034" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="3036" href="foundation.commuting-triangles-of-homotopies.html#2987" class="Bound">h</a><a id="3037" class="Symbol">)</a> <a id="3039" class="Symbol">(</a><a id="3040" href="foundation.commuting-triangles-of-homotopies.html#3040" class="Bound">top</a> <a id="3044" class="Symbol">:</a> <a id="3046" href="foundation.commuting-triangles-of-homotopies.html#2983" class="Bound">f</a> <a id="3048" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="3050" href="foundation.commuting-triangles-of-homotopies.html#2985" class="Bound">g</a><a id="3051" class="Symbol">)</a>
  <a id="3055" class="Keyword">where</a>

  <a id="3064" href="foundation.commuting-triangles-of-homotopies.html#3064" class="Function">right-whisker-concat-coherence-triangle-homotopies</a> <a id="3115" class="Symbol">:</a>
    <a id="3121" href="foundation.commuting-triangles-of-homotopies.html#917" class="Function">coherence-triangle-homotopies</a> <a id="3151" href="foundation.commuting-triangles-of-homotopies.html#3009" class="Bound">left</a> <a id="3156" href="foundation.commuting-triangles-of-homotopies.html#3024" class="Bound">right</a> <a id="3162" href="foundation.commuting-triangles-of-homotopies.html#3040" class="Bound">top</a> <a id="3166" class="Symbol">→</a>
    <a id="3172" class="Symbol">{</a><a id="3173" href="foundation.commuting-triangles-of-homotopies.html#3173" class="Bound">i</a> <a id="3175" class="Symbol">:</a> <a id="3177" class="Symbol">(</a><a id="3178" href="foundation.commuting-triangles-of-homotopies.html#3178" class="Bound">x</a> <a id="3180" class="Symbol">:</a> <a id="3182" href="foundation.commuting-triangles-of-homotopies.html#2953" class="Bound">A</a><a id="3183" class="Symbol">)</a> <a id="3185" class="Symbol">→</a> <a id="3187" href="foundation.commuting-triangles-of-homotopies.html#2965" class="Bound">B</a> <a id="3189" href="foundation.commuting-triangles-of-homotopies.html#3178" class="Bound">x</a><a id="3190" class="Symbol">}</a> <a id="3192" class="Symbol">(</a><a id="3193" href="foundation.commuting-triangles-of-homotopies.html#3193" class="Bound">H</a> <a id="3195" class="Symbol">:</a> <a id="3197" href="foundation.commuting-triangles-of-homotopies.html#2987" class="Bound">h</a> <a id="3199" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="3201" href="foundation.commuting-triangles-of-homotopies.html#3173" class="Bound">i</a><a id="3202" class="Symbol">)</a> <a id="3204" class="Symbol">→</a>
    <a id="3210" href="foundation.commuting-triangles-of-homotopies.html#917" class="Function">coherence-triangle-homotopies</a> <a id="3240" class="Symbol">(</a><a id="3241" href="foundation.commuting-triangles-of-homotopies.html#3009" class="Bound">left</a> <a id="3246" href="foundation-core.homotopies.html#3099" class="Function Operator">∙h</a> <a id="3249" href="foundation.commuting-triangles-of-homotopies.html#3193" class="Bound">H</a><a id="3250" class="Symbol">)</a> <a id="3252" class="Symbol">(</a><a id="3253" href="foundation.commuting-triangles-of-homotopies.html#3024" class="Bound">right</a> <a id="3259" href="foundation-core.homotopies.html#3099" class="Function Operator">∙h</a> <a id="3262" href="foundation.commuting-triangles-of-homotopies.html#3193" class="Bound">H</a><a id="3263" class="Symbol">)</a> <a id="3265" href="foundation.commuting-triangles-of-homotopies.html#3040" class="Bound">top</a>
  <a id="3271" href="foundation.commuting-triangles-of-homotopies.html#3064" class="Function">right-whisker-concat-coherence-triangle-homotopies</a> <a id="3322" href="foundation.commuting-triangles-of-homotopies.html#3322" class="Bound">T</a> <a id="3324" href="foundation.commuting-triangles-of-homotopies.html#3324" class="Bound">H</a> <a id="3326" href="foundation.commuting-triangles-of-homotopies.html#3326" class="Bound">x</a> <a id="3328" class="Symbol">=</a>
    <a id="3334" href="foundation.commuting-triangles-of-identifications.html#7682" class="Function">right-whisker-concat-coherence-triangle-identifications</a>
      <a id="3396" class="Symbol">(</a> <a id="3398" href="foundation.commuting-triangles-of-homotopies.html#3009" class="Bound">left</a> <a id="3403" href="foundation.commuting-triangles-of-homotopies.html#3326" class="Bound">x</a><a id="3404" class="Symbol">)</a>
      <a id="3412" class="Symbol">(</a> <a id="3414" href="foundation.commuting-triangles-of-homotopies.html#3024" class="Bound">right</a> <a id="3420" href="foundation.commuting-triangles-of-homotopies.html#3326" class="Bound">x</a><a id="3421" class="Symbol">)</a>
      <a id="3429" class="Symbol">(</a> <a id="3431" href="foundation.commuting-triangles-of-homotopies.html#3040" class="Bound">top</a> <a id="3435" href="foundation.commuting-triangles-of-homotopies.html#3326" class="Bound">x</a><a id="3436" class="Symbol">)</a>
      <a id="3444" class="Symbol">(</a> <a id="3446" href="foundation.commuting-triangles-of-homotopies.html#3324" class="Bound">H</a> <a id="3448" href="foundation.commuting-triangles-of-homotopies.html#3326" class="Bound">x</a><a id="3449" class="Symbol">)</a>
      <a id="3457" class="Symbol">(</a> <a id="3459" href="foundation.commuting-triangles-of-homotopies.html#3322" class="Bound">T</a> <a id="3461" href="foundation.commuting-triangles-of-homotopies.html#3326" class="Bound">x</a><a id="3462" class="Symbol">)</a>
</pre>
### Left whiskering of commuting triangles of homotopies with respect to composition

Consider a commuting triangle of homotopies

```text
        top
     f ----> g
      \     /
  left \   / right
        ∨ ∨
         h
```

where `f`, `g`, and `h` are maps `A → B`. Furthermore, consider a map
`i : B → X`. Then we obtain a commuting triangle of homotopies

```text
           i ·l top
     i ∘ f --------> i ∘ g
           \       /
  i ·l left \     / i ·l right
             \   /
              ∨ ∨
             i ∘ h.
```

This notion of whiskering should be compared to
[whiskering higher homotopies with respect to composition](foundation.whiskering-higher-homotopies-composition.md).

<pre class="Agda"><a id="4172" class="Keyword">module</a> <a id="4179" href="foundation.commuting-triangles-of-homotopies.html#4179" class="Module">_</a>
  <a id="4183" class="Symbol">{</a><a id="4184" href="foundation.commuting-triangles-of-homotopies.html#4184" class="Bound">l1</a> <a id="4187" href="foundation.commuting-triangles-of-homotopies.html#4187" class="Bound">l2</a> <a id="4190" href="foundation.commuting-triangles-of-homotopies.html#4190" class="Bound">l3</a> <a id="4193" class="Symbol">:</a> <a id="4195" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="4200" class="Symbol">}</a> <a id="4202" class="Symbol">{</a><a id="4203" href="foundation.commuting-triangles-of-homotopies.html#4203" class="Bound">A</a> <a id="4205" class="Symbol">:</a> <a id="4207" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4210" href="foundation.commuting-triangles-of-homotopies.html#4184" class="Bound">l1</a><a id="4212" class="Symbol">}</a> <a id="4214" class="Symbol">{</a><a id="4215" href="foundation.commuting-triangles-of-homotopies.html#4215" class="Bound">B</a> <a id="4217" class="Symbol">:</a> <a id="4219" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4222" href="foundation.commuting-triangles-of-homotopies.html#4187" class="Bound">l2</a><a id="4224" class="Symbol">}</a> <a id="4226" class="Symbol">{</a><a id="4227" href="foundation.commuting-triangles-of-homotopies.html#4227" class="Bound">X</a> <a id="4229" class="Symbol">:</a> <a id="4231" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="4234" href="foundation.commuting-triangles-of-homotopies.html#4190" class="Bound">l3</a><a id="4236" class="Symbol">}</a> <a id="4238" class="Symbol">(</a><a id="4239" href="foundation.commuting-triangles-of-homotopies.html#4239" class="Bound">i</a> <a id="4241" class="Symbol">:</a> <a id="4243" href="foundation.commuting-triangles-of-homotopies.html#4215" class="Bound">B</a> <a id="4245" class="Symbol">→</a> <a id="4247" href="foundation.commuting-triangles-of-homotopies.html#4227" class="Bound">X</a><a id="4248" class="Symbol">)</a>
  <a id="4252" class="Symbol">{</a><a id="4253" href="foundation.commuting-triangles-of-homotopies.html#4253" class="Bound">f</a> <a id="4255" href="foundation.commuting-triangles-of-homotopies.html#4255" class="Bound">g</a> <a id="4257" href="foundation.commuting-triangles-of-homotopies.html#4257" class="Bound">h</a> <a id="4259" class="Symbol">:</a> <a id="4261" href="foundation.commuting-triangles-of-homotopies.html#4203" class="Bound">A</a> <a id="4263" class="Symbol">→</a> <a id="4265" href="foundation.commuting-triangles-of-homotopies.html#4215" class="Bound">B</a><a id="4266" class="Symbol">}</a> <a id="4268" class="Symbol">(</a><a id="4269" href="foundation.commuting-triangles-of-homotopies.html#4269" class="Bound">left</a> <a id="4274" class="Symbol">:</a> <a id="4276" href="foundation.commuting-triangles-of-homotopies.html#4253" class="Bound">f</a> <a id="4278" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="4280" href="foundation.commuting-triangles-of-homotopies.html#4257" class="Bound">h</a><a id="4281" class="Symbol">)</a> <a id="4283" class="Symbol">(</a><a id="4284" href="foundation.commuting-triangles-of-homotopies.html#4284" class="Bound">right</a> <a id="4290" class="Symbol">:</a> <a id="4292" href="foundation.commuting-triangles-of-homotopies.html#4255" class="Bound">g</a> <a id="4294" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="4296" href="foundation.commuting-triangles-of-homotopies.html#4257" class="Bound">h</a><a id="4297" class="Symbol">)</a> <a id="4299" class="Symbol">(</a><a id="4300" href="foundation.commuting-triangles-of-homotopies.html#4300" class="Bound">top</a> <a id="4304" class="Symbol">:</a> <a id="4306" href="foundation.commuting-triangles-of-homotopies.html#4253" class="Bound">f</a> <a id="4308" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="4310" href="foundation.commuting-triangles-of-homotopies.html#4255" class="Bound">g</a><a id="4311" class="Symbol">)</a>
  <a id="4315" class="Keyword">where</a>

  <a id="4324" href="foundation.commuting-triangles-of-homotopies.html#4324" class="Function">left-whisker-comp-coherence-triangle-homotopies</a> <a id="4372" class="Symbol">:</a>
    <a id="4378" class="Symbol">(</a><a id="4379" href="foundation.commuting-triangles-of-homotopies.html#4379" class="Bound">T</a> <a id="4381" class="Symbol">:</a> <a id="4383" href="foundation.commuting-triangles-of-homotopies.html#917" class="Function">coherence-triangle-homotopies</a> <a id="4413" href="foundation.commuting-triangles-of-homotopies.html#4269" class="Bound">left</a> <a id="4418" href="foundation.commuting-triangles-of-homotopies.html#4284" class="Bound">right</a> <a id="4424" href="foundation.commuting-triangles-of-homotopies.html#4300" class="Bound">top</a><a id="4427" class="Symbol">)</a> <a id="4429" class="Symbol">→</a>
    <a id="4435" href="foundation.commuting-triangles-of-homotopies.html#917" class="Function">coherence-triangle-homotopies</a> <a id="4465" class="Symbol">(</a><a id="4466" href="foundation.commuting-triangles-of-homotopies.html#4239" class="Bound">i</a> <a id="4468" href="foundation.whiskering-homotopies-composition.html#2364" class="Function Operator">·l</a> <a id="4471" href="foundation.commuting-triangles-of-homotopies.html#4269" class="Bound">left</a><a id="4475" class="Symbol">)</a> <a id="4477" class="Symbol">(</a><a id="4478" href="foundation.commuting-triangles-of-homotopies.html#4239" class="Bound">i</a> <a id="4480" href="foundation.whiskering-homotopies-composition.html#2364" class="Function Operator">·l</a> <a id="4483" href="foundation.commuting-triangles-of-homotopies.html#4284" class="Bound">right</a><a id="4488" class="Symbol">)</a> <a id="4490" class="Symbol">(</a><a id="4491" href="foundation.commuting-triangles-of-homotopies.html#4239" class="Bound">i</a> <a id="4493" href="foundation.whiskering-homotopies-composition.html#2364" class="Function Operator">·l</a> <a id="4496" href="foundation.commuting-triangles-of-homotopies.html#4300" class="Bound">top</a><a id="4499" class="Symbol">)</a>
  <a id="4503" href="foundation.commuting-triangles-of-homotopies.html#4324" class="Function">left-whisker-comp-coherence-triangle-homotopies</a> <a id="4551" href="foundation.commuting-triangles-of-homotopies.html#4551" class="Bound">T</a> <a id="4553" href="foundation.commuting-triangles-of-homotopies.html#4553" class="Bound">x</a> <a id="4555" class="Symbol">=</a>
    <a id="4561" href="foundation.commuting-triangles-of-identifications.html#14158" class="Function">map-coherence-triangle-identifications</a> <a id="4600" href="foundation.commuting-triangles-of-homotopies.html#4239" class="Bound">i</a> <a id="4602" class="Symbol">(</a><a id="4603" href="foundation.commuting-triangles-of-homotopies.html#4269" class="Bound">left</a> <a id="4608" href="foundation.commuting-triangles-of-homotopies.html#4553" class="Bound">x</a><a id="4609" class="Symbol">)</a> <a id="4611" class="Symbol">(</a><a id="4612" href="foundation.commuting-triangles-of-homotopies.html#4284" class="Bound">right</a> <a id="4618" href="foundation.commuting-triangles-of-homotopies.html#4553" class="Bound">x</a><a id="4619" class="Symbol">)</a> <a id="4621" class="Symbol">(</a><a id="4622" href="foundation.commuting-triangles-of-homotopies.html#4300" class="Bound">top</a> <a id="4626" href="foundation.commuting-triangles-of-homotopies.html#4553" class="Bound">x</a><a id="4627" class="Symbol">)</a> <a id="4629" class="Symbol">(</a><a id="4630" href="foundation.commuting-triangles-of-homotopies.html#4551" class="Bound">T</a> <a id="4632" href="foundation.commuting-triangles-of-homotopies.html#4553" class="Bound">x</a><a id="4633" class="Symbol">)</a>
</pre>
### Right whiskering commuting triangles of homotopies with respect to composition

Consider a commuting triangle of homotopies

```text
        top
     f ----> g
      \     /
  left \   / right
        ∨ ∨
         h
```

where `f`, `g`, and `h` are maps `A → B`. Furthermore, consider a map
`i : X → A`. Then we obtain a commuting triangle of homotopies

```text
           top ·r i
     f ∘ i --------> g ∘ i
           \       /
  left ·r i \     / right ·r i
             \   /
              ∨ ∨
             h ∘ i.
```

This notion of whiskering should be compared to
[whiskering higher homotopies with respect to composition](foundation.whiskering-higher-homotopies-composition.md).

<pre class="Agda"><a id="5341" class="Keyword">module</a> <a id="5348" href="foundation.commuting-triangles-of-homotopies.html#5348" class="Module">_</a>
  <a id="5352" class="Symbol">{</a><a id="5353" href="foundation.commuting-triangles-of-homotopies.html#5353" class="Bound">l1</a> <a id="5356" href="foundation.commuting-triangles-of-homotopies.html#5356" class="Bound">l2</a> <a id="5359" href="foundation.commuting-triangles-of-homotopies.html#5359" class="Bound">l3</a> <a id="5362" class="Symbol">:</a> <a id="5364" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="5369" class="Symbol">}</a> <a id="5371" class="Symbol">{</a><a id="5372" href="foundation.commuting-triangles-of-homotopies.html#5372" class="Bound">A</a> <a id="5374" class="Symbol">:</a> <a id="5376" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5379" href="foundation.commuting-triangles-of-homotopies.html#5353" class="Bound">l1</a><a id="5381" class="Symbol">}</a> <a id="5383" class="Symbol">{</a><a id="5384" href="foundation.commuting-triangles-of-homotopies.html#5384" class="Bound">B</a> <a id="5386" class="Symbol">:</a> <a id="5388" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5391" href="foundation.commuting-triangles-of-homotopies.html#5356" class="Bound">l2</a><a id="5393" class="Symbol">}</a> <a id="5395" class="Symbol">{</a><a id="5396" href="foundation.commuting-triangles-of-homotopies.html#5396" class="Bound">X</a> <a id="5398" class="Symbol">:</a> <a id="5400" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="5403" href="foundation.commuting-triangles-of-homotopies.html#5359" class="Bound">l3</a><a id="5405" class="Symbol">}</a>
  <a id="5409" class="Symbol">{</a><a id="5410" href="foundation.commuting-triangles-of-homotopies.html#5410" class="Bound">f</a> <a id="5412" href="foundation.commuting-triangles-of-homotopies.html#5412" class="Bound">g</a> <a id="5414" href="foundation.commuting-triangles-of-homotopies.html#5414" class="Bound">h</a> <a id="5416" class="Symbol">:</a> <a id="5418" href="foundation.commuting-triangles-of-homotopies.html#5372" class="Bound">A</a> <a id="5420" class="Symbol">→</a> <a id="5422" href="foundation.commuting-triangles-of-homotopies.html#5384" class="Bound">B</a><a id="5423" class="Symbol">}</a> <a id="5425" class="Symbol">(</a><a id="5426" href="foundation.commuting-triangles-of-homotopies.html#5426" class="Bound">left</a> <a id="5431" class="Symbol">:</a> <a id="5433" href="foundation.commuting-triangles-of-homotopies.html#5410" class="Bound">f</a> <a id="5435" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="5437" href="foundation.commuting-triangles-of-homotopies.html#5414" class="Bound">h</a><a id="5438" class="Symbol">)</a> <a id="5440" class="Symbol">(</a><a id="5441" href="foundation.commuting-triangles-of-homotopies.html#5441" class="Bound">right</a> <a id="5447" class="Symbol">:</a> <a id="5449" href="foundation.commuting-triangles-of-homotopies.html#5412" class="Bound">g</a> <a id="5451" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="5453" href="foundation.commuting-triangles-of-homotopies.html#5414" class="Bound">h</a><a id="5454" class="Symbol">)</a> <a id="5456" class="Symbol">(</a><a id="5457" href="foundation.commuting-triangles-of-homotopies.html#5457" class="Bound">top</a> <a id="5461" class="Symbol">:</a> <a id="5463" href="foundation.commuting-triangles-of-homotopies.html#5410" class="Bound">f</a> <a id="5465" href="foundation-core.homotopies.html#2535" class="Function Operator">~</a> <a id="5467" href="foundation.commuting-triangles-of-homotopies.html#5412" class="Bound">g</a><a id="5468" class="Symbol">)</a>
  <a id="5472" class="Keyword">where</a>

  <a id="5481" href="foundation.commuting-triangles-of-homotopies.html#5481" class="Function">right-whisker-comp-coherence-triangle-homotopies</a> <a id="5530" class="Symbol">:</a>
    <a id="5536" class="Symbol">(</a><a id="5537" href="foundation.commuting-triangles-of-homotopies.html#5537" class="Bound">T</a> <a id="5539" class="Symbol">:</a> <a id="5541" href="foundation.commuting-triangles-of-homotopies.html#917" class="Function">coherence-triangle-homotopies</a> <a id="5571" href="foundation.commuting-triangles-of-homotopies.html#5426" class="Bound">left</a> <a id="5576" href="foundation.commuting-triangles-of-homotopies.html#5441" class="Bound">right</a> <a id="5582" href="foundation.commuting-triangles-of-homotopies.html#5457" class="Bound">top</a><a id="5585" class="Symbol">)</a> <a id="5587" class="Symbol">(</a><a id="5588" href="foundation.commuting-triangles-of-homotopies.html#5588" class="Bound">i</a> <a id="5590" class="Symbol">:</a> <a id="5592" href="foundation.commuting-triangles-of-homotopies.html#5396" class="Bound">X</a> <a id="5594" class="Symbol">→</a> <a id="5596" href="foundation.commuting-triangles-of-homotopies.html#5372" class="Bound">A</a><a id="5597" class="Symbol">)</a> <a id="5599" class="Symbol">→</a>
    <a id="5605" href="foundation.commuting-triangles-of-homotopies.html#917" class="Function">coherence-triangle-homotopies</a> <a id="5635" class="Symbol">(</a><a id="5636" href="foundation.commuting-triangles-of-homotopies.html#5426" class="Bound">left</a> <a id="5641" href="foundation.whiskering-homotopies-composition.html#2725" class="Function Operator">·r</a> <a id="5644" href="foundation.commuting-triangles-of-homotopies.html#5588" class="Bound">i</a><a id="5645" class="Symbol">)</a> <a id="5647" class="Symbol">(</a><a id="5648" href="foundation.commuting-triangles-of-homotopies.html#5441" class="Bound">right</a> <a id="5654" href="foundation.whiskering-homotopies-composition.html#2725" class="Function Operator">·r</a> <a id="5657" href="foundation.commuting-triangles-of-homotopies.html#5588" class="Bound">i</a><a id="5658" class="Symbol">)</a> <a id="5660" class="Symbol">(</a><a id="5661" href="foundation.commuting-triangles-of-homotopies.html#5457" class="Bound">top</a> <a id="5665" href="foundation.whiskering-homotopies-composition.html#2725" class="Function Operator">·r</a> <a id="5668" href="foundation.commuting-triangles-of-homotopies.html#5588" class="Bound">i</a><a id="5669" class="Symbol">)</a>
  <a id="5673" href="foundation.commuting-triangles-of-homotopies.html#5481" class="Function">right-whisker-comp-coherence-triangle-homotopies</a> <a id="5722" href="foundation.commuting-triangles-of-homotopies.html#5722" class="Bound">T</a> <a id="5724" href="foundation.commuting-triangles-of-homotopies.html#5724" class="Bound">i</a> <a id="5726" class="Symbol">=</a> <a id="5728" href="foundation.commuting-triangles-of-homotopies.html#5722" class="Bound">T</a> <a id="5730" href="foundation-core.function-types.html#455" class="Function Operator">∘</a> <a id="5732" href="foundation.commuting-triangles-of-homotopies.html#5724" class="Bound">i</a>
</pre>