# Uniqueness quantification

<pre class="Agda"><a id="38" class="Keyword">module</a> <a id="45" href="foundation.uniqueness-quantification%25E1%25B5%2589.html" class="Module">foundation.uniqueness-quantificationᵉ</a> <a id="83" class="Keyword">where</a>
</pre>
<details><summary>Imports</summary>

<pre class="Agda"><a id="139" class="Keyword">open</a> <a id="144" class="Keyword">import</a> <a id="151" href="foundation.dependent-pair-types%25E1%25B5%2589.html" class="Module">foundation.dependent-pair-typesᵉ</a>
<a id="184" class="Keyword">open</a> <a id="189" class="Keyword">import</a> <a id="196" href="foundation.torsorial-type-families%25E1%25B5%2589.html" class="Module">foundation.torsorial-type-familiesᵉ</a>
<a id="232" class="Keyword">open</a> <a id="237" class="Keyword">import</a> <a id="244" href="foundation.universe-levels%25E1%25B5%2589.html" class="Module">foundation.universe-levelsᵉ</a>

<a id="273" class="Keyword">open</a> <a id="278" class="Keyword">import</a> <a id="285" href="foundation-core.contractible-types%25E1%25B5%2589.html" class="Module">foundation-core.contractible-typesᵉ</a>
<a id="321" class="Keyword">open</a> <a id="326" class="Keyword">import</a> <a id="333" href="foundation-core.function-types%25E1%25B5%2589.html" class="Module">foundation-core.function-typesᵉ</a>
<a id="365" class="Keyword">open</a> <a id="370" class="Keyword">import</a> <a id="377" href="foundation-core.identity-types%25E1%25B5%2589.html" class="Module">foundation-core.identity-typesᵉ</a>
<a id="409" class="Keyword">open</a> <a id="414" class="Keyword">import</a> <a id="421" href="foundation-core.propositions%25E1%25B5%2589.html" class="Module">foundation-core.propositionsᵉ</a>
</pre>
</details>

## Idea

Given a predicate `P : A → Prop` we say there
{{#concept "uniquely exists" Disambiguation="in a subtype" WDID=Q2502253 WD="uniqueness quantification" Agda=∃!}}
_an `x : A` satisfying `P`_, if the [subtype](foundation-core.subtypes.md)
`Σ (x : A), (P x)` is [contractible](foundation-core.contractible-types.md).

More generally, given a [structure](foundation.structure.md) `B : A → 𝒰` we say
there
{{#concept "uniquely exists" Disambiguation="structure" Agda=uniquely-exists-structure}}
_an `x : A` and a `y : B x`_, if the
[total type](foundation.dependent-pair-types.md) `Σ (x : A), (B x)` is
contractible.

Note that the unique existence of structure is defined in the exact same way as
the concept of
[torsorial type families](foundation-core.torsorial-type-families.md). Whether
to use the concept of unique existence of a structure or the concept of
torsorial type family is dependent on the context. Torsoriality is used often to
emphasize the relation of the type family to the identity type, whereas
uniqueness of structure is used to emphasize the uniqueness of elements equipped
with further structure. For example, we tend to use unique existence in
combination with universal properties, in order to conclude that a certain map
equipped with some homotopies exists uniquely.

As a special case of uniqueness quantification, we recover
[exclusive disjunction](foundation.exclusive-disjunction.md) when the indexing
type is a [2-element type](univalent-combinatorics.2-element-types.md).
Concretely, we have the equivalence

```text
  ∃! (t : bool), (P t) ≐ is-contr (Σ (t : bool), (P t))
                       ≃ is-contr ((P false) + (P true))
                       ≐ P false ⊻ P true.
```

## Definitions

### Unique existence of structure

<pre class="Agda"><a id="2242" class="Keyword">module</a> <a id="2249" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2249" class="Module">_</a>
  <a id="2253" class="Symbol">{</a><a id="2254" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2254" class="Bound">l1ᵉ</a> <a id="2258" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2258" class="Bound">l2ᵉ</a> <a id="2262" class="Symbol">:</a> <a id="2264" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2269" class="Symbol">}</a> <a id="2271" class="Symbol">(</a><a id="2272" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2272" class="Bound">Aᵉ</a> <a id="2275" class="Symbol">:</a> <a id="2277" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2281" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2254" class="Bound">l1ᵉ</a><a id="2284" class="Symbol">)</a> <a id="2286" class="Symbol">(</a><a id="2287" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2287" class="Bound">Bᵉ</a> <a id="2290" class="Symbol">:</a> <a id="2292" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2272" class="Bound">Aᵉ</a> <a id="2295" class="Symbol">→</a> <a id="2297" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2301" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2258" class="Bound">l2ᵉ</a><a id="2304" class="Symbol">)</a>
  <a id="2308" class="Keyword">where</a>

  <a id="2317" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2317" class="Function">uniquely-exists-structure-Propᵉ</a> <a id="2349" class="Symbol">:</a> <a id="2351" href="foundation-core.propositions%25E1%25B5%2589.html#1181" class="Function">Propᵉ</a> <a id="2357" class="Symbol">(</a><a id="2358" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2254" class="Bound">l1ᵉ</a> <a id="2362" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2364" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2258" class="Bound">l2ᵉ</a><a id="2367" class="Symbol">)</a>
  <a id="2371" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2317" class="Function">uniquely-exists-structure-Propᵉ</a> <a id="2403" class="Symbol">=</a> <a id="2405" href="foundation.torsorial-type-families%25E1%25B5%2589.html#1187" class="Function">is-torsorial-Propᵉ</a> <a id="2424" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2287" class="Bound">Bᵉ</a>

  <a id="2430" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2430" class="Function">uniquely-exists-structureᵉ</a> <a id="2457" class="Symbol">:</a> <a id="2459" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2463" class="Symbol">(</a><a id="2464" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2254" class="Bound">l1ᵉ</a> <a id="2468" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2470" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2258" class="Bound">l2ᵉ</a><a id="2473" class="Symbol">)</a>
  <a id="2477" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2430" class="Function">uniquely-exists-structureᵉ</a> <a id="2504" class="Symbol">=</a> <a id="2506" href="foundation-core.propositions%25E1%25B5%2589.html#1288" class="Function">type-Propᵉ</a> <a id="2517" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2317" class="Function">uniquely-exists-structure-Propᵉ</a>

  <a id="2552" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2552" class="Function">is-prop-uniquely-exists-structureᵉ</a> <a id="2587" class="Symbol">:</a> <a id="2589" href="foundation-core.propositions%25E1%25B5%2589.html#1041" class="Function">is-propᵉ</a> <a id="2598" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2430" class="Function">uniquely-exists-structureᵉ</a>
  <a id="2627" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2552" class="Function">is-prop-uniquely-exists-structureᵉ</a> <a id="2662" class="Symbol">=</a>
    <a id="2668" href="foundation-core.propositions%25E1%25B5%2589.html#1361" class="Function">is-prop-type-Propᵉ</a> <a id="2687" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2317" class="Function">uniquely-exists-structure-Propᵉ</a>
</pre>
### Unique existence in a subtype

<pre class="Agda"><a id="2767" class="Keyword">module</a> <a id="2774" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2774" class="Module">_</a>
  <a id="2778" class="Symbol">{</a><a id="2779" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2779" class="Bound">l1ᵉ</a> <a id="2783" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2783" class="Bound">l2ᵉ</a> <a id="2787" class="Symbol">:</a> <a id="2789" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="2794" class="Symbol">}</a> <a id="2796" class="Symbol">(</a><a id="2797" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2797" class="Bound">Aᵉ</a> <a id="2800" class="Symbol">:</a> <a id="2802" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2806" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2779" class="Bound">l1ᵉ</a><a id="2809" class="Symbol">)</a> <a id="2811" class="Symbol">(</a><a id="2812" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2812" class="Bound">Pᵉ</a> <a id="2815" class="Symbol">:</a> <a id="2817" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2797" class="Bound">Aᵉ</a> <a id="2820" class="Symbol">→</a> <a id="2822" href="foundation-core.propositions%25E1%25B5%2589.html#1181" class="Function">Propᵉ</a> <a id="2828" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2783" class="Bound">l2ᵉ</a><a id="2831" class="Symbol">)</a>
  <a id="2835" class="Keyword">where</a>

  <a id="2844" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2844" class="Function">uniquely-exists-Propᵉ</a> <a id="2866" class="Symbol">:</a> <a id="2868" href="foundation-core.propositions%25E1%25B5%2589.html#1181" class="Function">Propᵉ</a> <a id="2874" class="Symbol">(</a><a id="2875" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2779" class="Bound">l1ᵉ</a> <a id="2879" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2881" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2783" class="Bound">l2ᵉ</a><a id="2884" class="Symbol">)</a>
  <a id="2888" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2844" class="Function">uniquely-exists-Propᵉ</a> <a id="2910" class="Symbol">=</a> <a id="2912" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2317" class="Function">uniquely-exists-structure-Propᵉ</a> <a id="2944" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2797" class="Bound">Aᵉ</a> <a id="2947" class="Symbol">(</a><a id="2948" href="foundation-core.propositions%25E1%25B5%2589.html#1288" class="Function">type-Propᵉ</a> <a id="2959" href="foundation-core.function-types%25E1%25B5%2589.html#476" class="Function Operator">∘ᵉ</a> <a id="2962" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2812" class="Bound">Pᵉ</a><a id="2964" class="Symbol">)</a>

  <a id="2969" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2969" class="Function">uniquely-existsᵉ</a> <a id="2986" class="Symbol">:</a> <a id="2988" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="2992" class="Symbol">(</a><a id="2993" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2779" class="Bound">l1ᵉ</a> <a id="2997" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="2999" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2783" class="Bound">l2ᵉ</a><a id="3002" class="Symbol">)</a>
  <a id="3006" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2969" class="Function">uniquely-existsᵉ</a> <a id="3023" class="Symbol">=</a> <a id="3025" href="foundation-core.propositions%25E1%25B5%2589.html#1288" class="Function">type-Propᵉ</a> <a id="3036" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2844" class="Function">uniquely-exists-Propᵉ</a>

  <a id="3061" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3061" class="Function">is-prop-uniquely-existsᵉ</a> <a id="3086" class="Symbol">:</a> <a id="3088" href="foundation-core.propositions%25E1%25B5%2589.html#1041" class="Function">is-propᵉ</a> <a id="3097" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2969" class="Function">uniquely-existsᵉ</a>
  <a id="3116" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3061" class="Function">is-prop-uniquely-existsᵉ</a> <a id="3141" class="Symbol">=</a> <a id="3143" href="foundation-core.propositions%25E1%25B5%2589.html#1361" class="Function">is-prop-type-Propᵉ</a> <a id="3162" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2844" class="Function">uniquely-exists-Propᵉ</a>

  <a id="3187" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3187" class="Function">∃!ᵉ</a> <a id="3191" class="Symbol">:</a> <a id="3193" href="foundation-core.propositions%25E1%25B5%2589.html#1181" class="Function">Propᵉ</a> <a id="3199" class="Symbol">(</a><a id="3200" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2779" class="Bound">l1ᵉ</a> <a id="3204" href="Agda.Primitive.html#961" class="Primitive Operator">⊔</a> <a id="3206" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2783" class="Bound">l2ᵉ</a><a id="3209" class="Symbol">)</a>
  <a id="3213" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3187" class="Function">∃!ᵉ</a> <a id="3217" class="Symbol">=</a> <a id="3219" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2844" class="Function">uniquely-exists-Propᵉ</a>
</pre>
### Components of unique existence

<pre class="Agda"><a id="3290" class="Keyword">module</a> <a id="3297" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3297" class="Module">_</a>
  <a id="3301" class="Symbol">{</a><a id="3302" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3302" class="Bound">l1ᵉ</a> <a id="3306" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3306" class="Bound">l2ᵉ</a> <a id="3310" class="Symbol">:</a> <a id="3312" href="Agda.Primitive.html#742" class="Postulate">Level</a><a id="3317" class="Symbol">}</a> <a id="3319" class="Symbol">{</a><a id="3320" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3320" class="Bound">Aᵉ</a> <a id="3323" class="Symbol">:</a> <a id="3325" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="3329" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3302" class="Bound">l1ᵉ</a><a id="3332" class="Symbol">}</a> <a id="3334" class="Symbol">{</a><a id="3335" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3335" class="Bound">Bᵉ</a> <a id="3338" class="Symbol">:</a> <a id="3340" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3320" class="Bound">Aᵉ</a> <a id="3343" class="Symbol">→</a> <a id="3345" href="Agda.Primitive.html#429" class="Primitive">UUᵉ</a> <a id="3349" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3306" class="Bound">l2ᵉ</a><a id="3352" class="Symbol">}</a>
  <a id="3356" class="Keyword">where</a>

  <a id="3365" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3365" class="Function">pair-uniquely-existsᵉ</a> <a id="3387" class="Symbol">:</a> <a id="3389" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2430" class="Function">uniquely-exists-structureᵉ</a> <a id="3416" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3320" class="Bound">Aᵉ</a> <a id="3419" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3335" class="Bound">Bᵉ</a> <a id="3422" class="Symbol">→</a> <a id="3424" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="3427" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3320" class="Bound">Aᵉ</a> <a id="3430" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3335" class="Bound">Bᵉ</a>
  <a id="3435" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3365" class="Function">pair-uniquely-existsᵉ</a> <a id="3457" class="Symbol">=</a> <a id="3459" href="foundation-core.contractible-types%25E1%25B5%2589.html#1016" class="Function">centerᵉ</a>

  <a id="3470" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3470" class="Function">pr1-uniquely-existsᵉ</a> <a id="3491" class="Symbol">:</a> <a id="3493" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2430" class="Function">uniquely-exists-structureᵉ</a> <a id="3520" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3320" class="Bound">Aᵉ</a> <a id="3523" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3335" class="Bound">Bᵉ</a> <a id="3526" class="Symbol">→</a> <a id="3528" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3320" class="Bound">Aᵉ</a>
  <a id="3533" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3470" class="Function">pr1-uniquely-existsᵉ</a> <a id="3554" class="Symbol">=</a> <a id="3556" href="foundation.dependent-pair-types%25E1%25B5%2589.html#697" class="Field">pr1ᵉ</a> <a id="3561" href="foundation-core.function-types%25E1%25B5%2589.html#476" class="Function Operator">∘ᵉ</a> <a id="3564" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3365" class="Function">pair-uniquely-existsᵉ</a>

  <a id="3589" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3589" class="Function">pr2-uniquely-existsᵉ</a> <a id="3610" class="Symbol">:</a>
    <a id="3616" class="Symbol">(</a><a id="3617" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3617" class="Bound">pᵉ</a> <a id="3620" class="Symbol">:</a> <a id="3622" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2430" class="Function">uniquely-exists-structureᵉ</a> <a id="3649" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3320" class="Bound">Aᵉ</a> <a id="3652" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3335" class="Bound">Bᵉ</a><a id="3654" class="Symbol">)</a> <a id="3656" class="Symbol">→</a> <a id="3658" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3335" class="Bound">Bᵉ</a> <a id="3661" class="Symbol">(</a><a id="3662" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3470" class="Function">pr1-uniquely-existsᵉ</a> <a id="3683" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3617" class="Bound">pᵉ</a><a id="3685" class="Symbol">)</a>
  <a id="3689" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3589" class="Function">pr2-uniquely-existsᵉ</a> <a id="3710" class="Symbol">=</a> <a id="3712" href="foundation.dependent-pair-types%25E1%25B5%2589.html#711" class="Field">pr2ᵉ</a> <a id="3717" href="foundation-core.function-types%25E1%25B5%2589.html#476" class="Function Operator">∘ᵉ</a> <a id="3720" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3365" class="Function">pair-uniquely-existsᵉ</a>

  <a id="3745" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3745" class="Function">contraction-uniquely-existsᵉ</a> <a id="3774" class="Symbol">:</a>
    <a id="3780" class="Symbol">(</a><a id="3781" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3781" class="Bound">pᵉ</a> <a id="3784" class="Symbol">:</a> <a id="3786" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#2430" class="Function">uniquely-exists-structureᵉ</a> <a id="3813" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3320" class="Bound">Aᵉ</a> <a id="3816" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3335" class="Bound">Bᵉ</a><a id="3818" class="Symbol">)</a> <a id="3820" class="Symbol">→</a>
    <a id="3826" class="Symbol">(</a><a id="3827" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3827" class="Bound">qᵉ</a> <a id="3830" class="Symbol">:</a> <a id="3832" href="foundation.dependent-pair-types%25E1%25B5%2589.html#585" class="Record">Σᵉ</a> <a id="3835" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3320" class="Bound">Aᵉ</a> <a id="3838" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3335" class="Bound">Bᵉ</a><a id="3840" class="Symbol">)</a> <a id="3842" class="Symbol">→</a> <a id="3844" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3365" class="Function">pair-uniquely-existsᵉ</a> <a id="3866" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3781" class="Bound">pᵉ</a> <a id="3869" href="foundation-core.identity-types%25E1%25B5%2589.html#2730" class="Function Operator">＝ᵉ</a> <a id="3872" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3827" class="Bound">qᵉ</a>
  <a id="3877" href="foundation.uniqueness-quantification%25E1%25B5%2589.html#3745" class="Function">contraction-uniquely-existsᵉ</a> <a id="3906" class="Symbol">=</a> <a id="3908" href="foundation-core.contractible-types%25E1%25B5%2589.html#1413" class="Function">contractionᵉ</a>
</pre>
## See also

- Unique existence is the indexed counterpart to
  [exclusive disjunction](foundation.exclusive-disjunction.md).
- A different name for _unique existence_ is
  [torsoriality](foundation.torsorial-type-families.md).

## External links

- [uniqueness quantifier](https://ncatlab.org/nlab/show/uniqueness+quantifier)
  at $n$Lab
- [Uniqueness quantification](https://en.wikipedia.org/wiki/Uniqueness_quantification)
  at Wikipedia