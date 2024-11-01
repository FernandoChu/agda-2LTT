# The action on identifications of dependent functions

<pre class="Agda"><a id="65" class="Keyword">module</a> <a id="72" href="foundation.action-on-identifications-dependent-functions.html" class="Module">foundation.action-on-identifications-dependent-functions</a> <a id="129" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="185" class="Keyword">open</a> <a id="190" class="Keyword">import</a> <a id="197" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>

<a id="225" class="Keyword">open</a> <a id="230" class="Keyword">import</a> <a id="237" href="foundation-core.dependent-identifications.html" class="Module">foundation-core.dependent-identifications</a>
<a id="279" class="Keyword">open</a> <a id="284" class="Keyword">import</a> <a id="291" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
</pre>
</details>

## Idea

Given a dependent function `f : (x : A) → B x` and an
[identification](foundation-core.identity-types.md) `p : x ＝ y` in `A`, we
cannot directly compare the values `f x` and `f y`, since `f x` is an element of
type `B x` while `f y` is an element of type `B y`. However, we can
[transport](foundation-core.transport-along-identifications.md) the value `f x`
along `p` to obtain an element of type `B y` that is comparable to the value
`f y`. In other words, we can consider the type of
[dependent identifications](foundation-core.dependent-identifications.md) over
`p` from `f x` to `f y`. The **dependent action on identifications** of `f` on
`p` is a dependent identification

```text
  apd f p : dependent-identification B p (f x) (f y).
```

## Definition

### Functorial action of dependent functions on identity types

<pre class="Agda"><a id="apd"></a><a id="1181" href="foundation.action-on-identifications-dependent-functions.html#1181" class="Function">apd</a> <a id="1185" class="Symbol">:</a>
  <a id="1189" class="Symbol">{</a><a id="1190" href="foundation.action-on-identifications-dependent-functions.html#1190" class="Bound">l1</a> <a id="1193" href="foundation.action-on-identifications-dependent-functions.html#1193" class="Bound">l2</a> <a id="1196" class="Symbol">:</a> <a id="1198" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="1203" class="Symbol">}</a> <a id="1205" class="Symbol">{</a><a id="1206" href="foundation.action-on-identifications-dependent-functions.html#1206" class="Bound">A</a> <a id="1208" class="Symbol">:</a> <a id="1210" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1213" href="foundation.action-on-identifications-dependent-functions.html#1190" class="Bound">l1</a><a id="1215" class="Symbol">}</a> <a id="1217" class="Symbol">{</a><a id="1218" href="foundation.action-on-identifications-dependent-functions.html#1218" class="Bound">B</a> <a id="1220" class="Symbol">:</a> <a id="1222" href="foundation.action-on-identifications-dependent-functions.html#1206" class="Bound">A</a> <a id="1224" class="Symbol">→</a> <a id="1226" href="Agda.Primitive.html#388" class="Primitive">UU</a> <a id="1229" href="foundation.action-on-identifications-dependent-functions.html#1193" class="Bound">l2</a><a id="1231" class="Symbol">}</a> <a id="1233" class="Symbol">(</a><a id="1234" href="foundation.action-on-identifications-dependent-functions.html#1234" class="Bound">f</a> <a id="1236" class="Symbol">:</a> <a id="1238" class="Symbol">(</a><a id="1239" href="foundation.action-on-identifications-dependent-functions.html#1239" class="Bound">x</a> <a id="1241" class="Symbol">:</a> <a id="1243" href="foundation.action-on-identifications-dependent-functions.html#1206" class="Bound">A</a><a id="1244" class="Symbol">)</a> <a id="1246" class="Symbol">→</a> <a id="1248" href="foundation.action-on-identifications-dependent-functions.html#1218" class="Bound">B</a> <a id="1250" href="foundation.action-on-identifications-dependent-functions.html#1239" class="Bound">x</a><a id="1251" class="Symbol">)</a> <a id="1253" class="Symbol">{</a><a id="1254" href="foundation.action-on-identifications-dependent-functions.html#1254" class="Bound">x</a> <a id="1256" href="foundation.action-on-identifications-dependent-functions.html#1256" class="Bound">y</a> <a id="1258" class="Symbol">:</a> <a id="1260" href="foundation.action-on-identifications-dependent-functions.html#1206" class="Bound">A</a><a id="1261" class="Symbol">}</a>
  <a id="1265" class="Symbol">(</a><a id="1266" href="foundation.action-on-identifications-dependent-functions.html#1266" class="Bound">p</a> <a id="1268" class="Symbol">:</a> <a id="1270" href="foundation.action-on-identifications-dependent-functions.html#1254" class="Bound">x</a> <a id="1272" href="foundation-core.identity-types.html#2713" class="Function Operator">＝</a> <a id="1274" href="foundation.action-on-identifications-dependent-functions.html#1256" class="Bound">y</a><a id="1275" class="Symbol">)</a> <a id="1277" class="Symbol">→</a> <a id="1279" href="foundation-core.dependent-identifications.html#964" class="Function">dependent-identification</a> <a id="1304" href="foundation.action-on-identifications-dependent-functions.html#1218" class="Bound">B</a> <a id="1306" href="foundation.action-on-identifications-dependent-functions.html#1266" class="Bound">p</a> <a id="1308" class="Symbol">(</a><a id="1309" href="foundation.action-on-identifications-dependent-functions.html#1234" class="Bound">f</a> <a id="1311" href="foundation.action-on-identifications-dependent-functions.html#1254" class="Bound">x</a><a id="1312" class="Symbol">)</a> <a id="1314" class="Symbol">(</a><a id="1315" href="foundation.action-on-identifications-dependent-functions.html#1234" class="Bound">f</a> <a id="1317" href="foundation.action-on-identifications-dependent-functions.html#1256" class="Bound">y</a><a id="1318" class="Symbol">)</a>
<a id="1320" href="foundation.action-on-identifications-dependent-functions.html#1181" class="Function">apd</a> <a id="1324" href="foundation.action-on-identifications-dependent-functions.html#1324" class="Bound">f</a> <a id="1326" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a> <a id="1331" class="Symbol">=</a> <a id="1333" href="foundation-core.identity-types.html#2682" class="InductiveConstructor">refl</a>
</pre>
## See also

- [Action of functions on identifications](foundation.action-on-identifications-functions.md)
- [Action of functions on higher identifications](foundation.action-on-higher-identifications-functions.md).
- [Action of binary functions on identifications](foundation.action-on-identifications-binary-functions.md).
