---
marp: true
theme: default
paginate: true
style: |
  :root {
    --accent: #4a6cf7;
  }
  section {
    font-family: 'Avenir Next', 'Segoe UI', 'Helvetica Neue', sans-serif;
    font-size: 26px;
    line-height: 1.32;
    padding: 34px 52px;
    letter-spacing: -0.005em;
  }
  h1, h2 {
    color: #1a2540;
    letter-spacing: -0.02em;
  }
  h1 {
    font-size: 1.65em;
    margin: 0 0 0.35em;
  }
  h2 {
    font-size: 1.3em;
    border-bottom: 3px solid var(--accent);
    padding-bottom: 0.15em;
    margin: 0 0 0.45em;
  }
  h3 {
    color: var(--accent);
    font-weight: 600;
    font-size: 1.08em;
    margin: 0.45em 0 0.2em;
  }
  p, ul, ol {
    margin: 0.3em 0;
  }
  ul, ol {
    padding-left: 1.05em;
  }
  li {
    margin: 0.1em 0;
  }
  li > ul, li > ol {
    margin: 0.05em 0;
  }
  a {
    color: var(--accent);
    text-decoration: none;
  }
  blockquote {
    border-left: 5px solid var(--accent);
    background: #f4f6fd;
    border-radius: 0 10px 10px 0;
    padding: 0.4em 0.9em;
    margin: 0.45em 0;
    font-style: italic;
    font-size: 1em;
    color: #2a3550;
  }
  blockquote p {
    margin: 0.15em 0;
  }
  blockquote footer, blockquote .cite-by {
    font-style: normal;
    font-size: 0.78em;
    color: #6b7390;
    margin-top: 0.35em;
  }
  pre {
    font-size: 0.62em;
    line-height: 1.22;
    margin: 0.4em 0;
    padding: 0.55em 0.75em;
  }
  code {
    font-size: 0.86em;
  }
  table {
    font-size: 0.76em;
    margin: 0.4em 0;
  }
  th, td {
    padding: 0.22em 0.5em;
  }
  img {
    max-height: 460px;
  }
  section::after {
    color: #9aa3bd;
    font-size: 0.5em;
  }
  /* Extra-dense slide: add <!-- _class: dense --> to a slide */
  section.dense {
    font-size: 21px;
    padding: 26px 42px;
    line-height: 1.25;
  }
  section.dense pre { font-size: 0.58em; }
  section.dense table { font-size: 0.7em; }
  
---
# ACL2 for Trustworthy AI
Jim White <mailto:jim@wiki3.ai>
November 16th, 2026
[20th International Workshop on the ACL2 Theorem Prover
and Its Applications (ACL2-2026)](https://www.cs.utexas.edu/~moore/acl2/workshop-2026/index.html)
Menlo Park, California, USA

---


## Douglas Bruce Lenat (September 13, 1950 – August 31, 2023)

### AI has lost a giant

Gary Marcus, September 1st, 2023

> If people like Marvin Minsky, John McCarthy, and Allen Newell were among the first to think deeply about how symbolic AI, in which machines manipulate explicit verbal-like representations, might work, Doug was the first to try really hard to make it actually work.  

https://garymarcus.substack.com/p/doug-lenat-1950-2023  

https://stanfordmag.org/contents/he-taught-ai-the-facts-of-life


---

## Why Do We Need Trustworthy AI?

- **ByBit:** The $1.5B Bybit hack was pulled off primarily through social engineering and supply-chain compromise — a Safe{Wallet} developer was tricked into running malicious software, allowing attackers to inject code that deceived Bybit's signers — with AI playing, at most, a supporting role in fabricated identities. [chainalysis](https://www.chainalysis.com/blog/bybit-exchange-hack-february-2025-crypto-security-dprk/)

- **Binance:** In the $6.3B Binance heist, AI played a direct role at multiple stages — a tampered AI coding tool started the compromise, AI-assisted fake job interviews built trust, and attackers hijacked Binance's own internal AI tool to reach the wallet infrastructure team. [reuters](https://www.reuters.com/world/binance-says-hackers-used-fake-job-interview-compromise-computer-before-63-2026-11-03/)

- **ByBit:** AI played, at most, a supporting role — the confirmed vector was social engineering of a Safe{Wallet} developer and malicious code injection, with no evidence AI drove the breach itself. [chainalysis](https://www.chainalysis.com/blog/bybit-exchange-hack-february-2025-crypto-security-dprk/)

- **Binance:** Hackers' entry point was "vibe coding" gone wrong — an engineer downloaded a tampered AI coding tool, and attackers later hijacked Binance's own internal AI tool as a springboard to seize control of wallet-infrastructure machines. [reuters](https://www.reuters.com/world/binance-says-hackers-used-fake-job-interview-compromise-computer-before-63-2026-11-03/)

- **South Korean banks:** The October 2026 breaches across 16 financial firms (~100,000 customer records) show traces of ARTEX, a free open-source AI penetration-testing agent (built on DeepSeek) that autonomously finds and exploits vulnerabilities — with CrowdStrike assessing a financially motivated Chinese-speaking actor behind it. [fdd](https://www.fdd.org/analysis/ai-assisted-bank-hacks-expose-a-blind-spot-in-south-koreas-cyber-defenses/)

---

## What Does Trustworthy AI Mean?

### Lenat's Last Paper

> **Getting from Generative AI to Trustworthy AI:**
> *What LLMs might learn from Cyc*
> <div class="cite-by">Doug Lenat &amp; Gary Marcus · arXiv:2308.04445 · 2023</div>

[📄 arxiv.org/abs/2308.04445](https://arxiv.org/abs/2308.04445)  [Submitted on 31 Jul 2023]

> We suggest that any trustworthy general AI will need to hybridize the approaches, the LLM approach and more formal approach, and lay out a path to realizing that dream.



---

## Criteria for a Trustworthy AI

- **Explain an answer.** Trace each inference to its premises and identify the source of each fact or rule.
- **Reason in several ways.** Deduce consequences, generalize from examples, draw analogies, and infer likely explanations.
- **Interpret claims in context.** Track who believes what, how quantifiers are scoped, what is possible or necessary, and where a claim applies.
- **Revise judgments.** Weigh arguments for and against each answer, recognize exceptions, and update conclusions when evidence changes.
- **Know its limits and obligations.** Assess its own knowledge and abilities. Make its ethical principles inspectable and explain how it resolves conflicts.
- **Meet the demands of the task.** Draw on broad and deep knowledge, respond in time, and use language, perception, and physical action as needed.

*Adapted from Doug Lenat and Gary Marcus, “Getting from Generative AI to Trustworthy AI” (2023), §2. The authors’ 16 criteria are grouped here into six.*

---

# Six criteria, and where each comes from

| Criterion | Lenat & Marcus 2023 | NIST AI RMF 1.0 | U.S. Gov (Jan 2025) | ACL2 artifact |
|---|---|---|---|---|
| Checkable | #1 explanation to first principles | explainable & interpretable | "rigorous" | proof object; Milawa/ACL2Lean re-check |
| Traceable | #1 provenance, #12 meta-knowledge | accountable & transparent | "technical evidence packages" | book checksums + rule dependencies |
| Repeatable | — (their "unstable" complaint) | valid and reliable | "repeatable" | pure evaluation; daily re-certification |
| Knows its limits | #6 model of what it does not know | safe | — | verified abstention / `must-respond-p` |
| Bounded | #13 the "immutable kernel contract" | secure & resilient | — | `permission-safety`, budget, termination |
| Rapid | #14 sufficient speed | — | "rapid" | Smtlink3, Axe, ATC |


---

# Lenat's criteria for a Trustworthy AI  (2023)

*"A trustworthy AI… the full step-by-step line of reasoning is always available,
and for each step the provenance of the knowledge used can be documented and audited."*

1. **Justified, not just right** — every answer survives repeated "why?", bottoming out in
   first principles, with a source for each step. *(#1, #12)*
2. **Reasons the way people do** — deduction, induction, abduction, analogy, and contradiction
   detection, at human depth. *(#2–#5)*
3. **Speaks real logic** — quantifier scope and nested modals ("Ukraine hopes that the U.S.
   believes that Putin plans to…") handled without flinching. *(#7, #8)*
4. **Provisional by design** — almost everything is true-by-default; arguments are weighed pro
   and con; new information *retracts* old conclusions, and it tells you. *(#9, #10)*
5. **Situated and bounded** — knows the context, the culture, what *you* already know, its own
   limits, and the contract it is operating under — while being fast, broadly knowledgeable,
   and able to act in the world. *(#6, #11, #13–#16)*

> Lenat & Marcus, *Getting from Generative AI to Trustworthy AI*, arXiv:2308.04445 — 16 desiderata, §2


---


# Lenat's criteria for a Trustworthy AI  (16 desiderata → five)

| Criterion | In his words | For us |
|---|---|---|
| **Justified** (#1, #12) | reasoning chain to first principles + provenance per step | a proof object is the only artifact that meets this |
| **Reasons like a person** (#2–#5) | deduction, induction, abduction, analogy | we do deduction well; say plainly where we don't |
| **Speaks real logic** (#7, #8) | quantifiers, nested modals, flavors of negation | scope is explicit and checkable at zero cost |
| **Provisional** (#9, #10) | true-by-default, pro/con arguments, retraction | monotone proofs can't retract — dependency graphs can |
| **Situated & bounded** (#6, #11, #13–#16) | contexts, theory of mind, an inspectable ethical "contract", speed, embodiment | microtheories ≈ locales/books; the contract ≈ a verified kernel |



---


# 1 · Explain an answer

**Trace each inference to its premises; name the source of every fact and rule.** *(#1, #12)*

> *"How many thumbs did Lincoln's maternal grandmother's mother have?"*
> Answered on a laptop — with the chain available for inspection, step by step.

**Today:** an LLM's explanation is narration, not derivation. When researchers planted hints that
changed the model's answer, the chain of thought mentioned the hint **below 20%** of the time it
was actually used (arXiv:2505.05410). And untraceable claims now have a body count: **2,292** court
decisions involving fabricated authorities, as of this morning *(Charlotin database)*.

*↳ A proof object is an explanation a stranger can re-check without trusting you.*


---


# 2 · Reason in several ways

**Deduce; generalize from examples; draw analogies; infer the best explanation.** *(#2–#5)*

> *Why are Bullwinkle the Moose and Mickey Mouse not the same individual?* Not by storing 10²⁰
> pairwise facts — but by one rule: **taxa that do not specialize one another are disjoint**,
> plus the Linnaean taxonomy. One axiom buys a hundred million conclusions.

**Today:** deduction has improved enormously — reasoning models with verifiable rewards, prover-
integrated search. What hasn't: robustness. Accuracy drops when *only the numbers change*
(GSM-Symbolic, arXiv:2410.05229) and collapses at high compositional depth regardless of how long
the model "thinks" (arXiv:2506.06941).

*↳ We supply the sound half of this honestly — and say plainly that induction over data isn't ours.*

---


# 3 · Interpret claims in context

**Track who believes what, how quantifiers are scoped, what is possible, where a claim applies.**
*(#6, #7, #8, #11)*

> *"Every Swede has a king"* — one king. *"Every Swede has a mother"* — not one mother.
> *"Ukraine hopes that the U.S. believes that Putin plans to…"* — three nested attitudes.
> Cyc answers "name a Jedi" inside the *StarWars* context and "there are none" in *RealWorld*,
> without contradiction, because each assertion lives in a named microtheory.

**Today:** scope is implicit and therefore unstable — transformers degrade on quantifier tracking
and multi-hop composition (Faith & Fate, NeurIPS 2023), and accuracy falls as embedding depth grows.
Worse, context *conflation*: the web contains both "Luke is Vader's son" and "no Jedi exist," with
nothing marking which world each is true in.

*↳ Skolemization makes scope free; locales/theories are microtheories with soundness theorems.*


---


# 4 · Revise judgments

**Weigh arguments pro and con, recognize exceptions, update when evidence changes.** *(#9, #10)*

> Most Spaniards speak Spanish at home. Most **Vitoria** residents speak Basque. Fred lives in
> Vitoria. There is an argument for Spanish and a *preferred* argument for Basque — and a weak,
> very general argument against Basque that loses to both. Teachers are sedentary; gym teachers are
> an exception; **this person is an exception to the exception.**
> And: *"it might need to actively inform others that it's retracting… some response it gave them in
> the past."*

**Today:** there is no belief state to revise. Retrieval appends text, fine-tuning overwrites
weights, and nothing records which conclusions depended on what — so a retraction cannot propagate.

*↳ Monotone proofs can't retract — but dependency tracking can: change an axiom, learn exactly which
theorems lost their support. Nobody has built this over the ACL2 books.*


---


# 5 · Know its limits and obligations

**Assess its own knowledge and abilities; make ethical principles inspectable; explain conflicts.**
*(#12, #13)*

> *"Wild guesses should not be advanced as blithely as those supported by strong arguments."*
> His ethics requirement is unusually concrete: the corpus of principles must be **"explicitly known
> and inspectable by everyone it is affecting,"** with a small **immutable kernel** — the contract
> between an AI and its users.

**Today:** guessing is *incentivized*. Kalai, Nachum, Vempala & Zhang argue models hallucinate
because training and scoring reward guessing over acknowledging uncertainty (arXiv:2509.04664) — and
their proposed fix changes benchmark scoring, not the model. Meanwhile a constitution is prose: no
one can ask whether it is consistent, or whether a policy violates it.

*↳ Verified abstention (`must-respond-p`) and a machine-checked policy kernel: the contract as an artifact.*


---


# 6 · Meet the demands of the task

**Broad and deep knowledge; respond in time; language, perception, action as needed.** *(#14–#16)*

> Cyc carries tens of millions of hand-authored default-true axioms and ~10,000 contexts; four
> decades and **2,000 person-years** went into it. Speed came from **1,100 specialized reasoners** —
> not from theorem proving: footnote 9 admits the general prover was quietly switched off after a
> million consecutive timeouts.

**Today:** this is the criterion LLMs **win outright** — breadth, latency, language, perception.
Say it out loud. What they paid for it is criteria 1–5: no provenance, nothing to revise, no contract.
Both papers end at the same place: hybridize.

*↳ This is also our lesson: decidable fragments + specialized engines (Smtlink3, Axe, ATC) — the
lesson SAT learned and Cyc learned independently.*


---

## 1 · Explain an answer

> A trustworthy AI should be able to recount its line of reasoning behind any answer it gives.
Asking a series of repeated **Why is that?** follow-up questions should elicit increasingly
fundamental knowledge, ultimately bottoming out in first principles and 'given' ground truths.
Each piece of evidence, knowledge, rule of thumb, etc. invoked in that reasoning chain should also
have its source or provenance known.  *(#1)*

**His example:** a physician asked ChatGPT for the source of an unexpected answer. *"It took a real
journal, the European Journal of Internal Medicine. It took the last names and first names… of authors
who have published in said journal. And it confabulated out of thin air [the title of] a study…"*

**His verdict:** *"LLMs' inability to soundly explain how they came to their conclusions and what actual
trustworthy (or not) knowledge is the basis for those intermediate steps renders them unsuitable for
large classes of applications that require soundness, trust, and auditability."*

[2026: chain-of-thought disclosure rate below 20% when a planted hint was used — arXiv:2505.05410.]


---


## 2 · Reason in several ways

> A trustworthy AI should be able to perform the same types of deductions as people do, as deeply as people generally reason.  *(#2–#5)*

> If you know that countries have borders, and Andorra is a country, then you can infer that Andorra has borders.

> If someone enters a room that had four people, it now has five.

> A checkmated chess player considers the tree of all moves and counter-moves… and tips over their king.

> A newly discovered invertebrate, *a dwim*, seen with eight legs and two wings → most dwims have eight legs and two wings. 

---

## Abductive Reasoning

> Abductive Reasoning, sometimes known as inference to the best explanation. If a janitor sees a set of chairs in a room that looks like the set of chairs the janitor observed the night before, the presumption, possibly incorrect, but best explanation, other things being equal, is that it is the same set of chairs. This kind of reasoning can lead to errors but, like induction and analogy, it is so useful that we do it all the time.

**His verdict:** *"The current LLM-based chatbots aren't so much understanding and inferring as remembering
and espousing."*  And: *"after ChatGPT told us that Romeo commits suicide at the end of Romeo and Juliet, we
asked whether Romeo dies during the play, and it said there was no way to know!"*

[2026: this criterion improved most — reasoning models with verifiable rewards; accuracy still degrades with clause count (arXiv:2410.05229) and collapses at depth (arXiv:2506.06941).]


---

## 3 · Interpret claims in context

> Consider 'Every Swede has a king' versus 'Every Swede has a mother' — each person in Sweden of course has the same king but not every Swede shares the same mother!  *(#7)*

> …quite deep nestings of such, e.g., 'Ukraine hopes that the U.S. believes that Putin plans to…'  *(#8)*  

> Some pieces of advice apply at football games but not classroom lectures.  *(#11)*

**Example:** Cyc answers in the *StarWars* context and names several Jedi, which does not contradict the same question being asked in the RealWorld context and answering that there are no Jedi.

**His verdict on why this breaks with training on text:** *"Most human communication leaves some elements of
the context implicit, which can lead to, e.g., conflation when training an LLM."*  And on expressiveness:
limiting an AI to knowledge graphs or propositional logic — *"a huge barrier to it ever becoming a trustworthy
general AI."*

[2026: quantifier tracking and multi-hop composition remain weak (Faith & Fate, NeurIPS 2023).]


---


## 4 · Revise judgments

> Much of what one hears, reads, says, believes, and reasons with is only true by default… To be trustworthy, an AI needs to be able to assimilate new information and revise its earlier beliefs and earlier answers. For some critical applications, it might need to actively inform others that it's retracting and revising some response it gave them in the past.  *(#9)*

> Teachers today are typically sedentary, but gym teachers are an exception, but this particular person is an exception to that exception, but while recuperating… etc.

> Fred: most Spaniards speak Spanish at home, most residents of Vitoria speak Basque, Fred lives in Vitoria — *"more specific ones trump more general ones."*  His preference heuristics: *"prefer recent ones to stale ones, short ones to long ones, expert ones to novice ones, constructive ones to nonconstructive.

**His verdict:** LLMs and Cyc sit at opposite poles, *"in which essentially neither knowledge nor reasoning is
explicit"* — and what is not explicit cannot be retracted.  *(fn 3: as we age we retain "stale" conclusions;
*"AIs can do better than people at this."*)*

[2026: retrieval appends text, fine-tuning overwrites weights; nothing records which conclusion depended on which premise.]


---


## 5 · Know its limits and obligations

> Wild guesses should not be advanced as blithely as those supported by strong arguments.  *(#12)*  

> A model of self including a good model of what it does and doesn't know, and a good model of what it is and isn't
capable of and what its 'contract' with this user currently is.  *(#6)*

> A trustworthy AI should follow a core of guiding principles which appear inviolate, such as not lying or causing emotional or physical harm"* — though *"these are often shaded and complicated and conflicting (e.g., lying to someone so as not to unnecessarily hurt them; a doctor snapping a dislocated shoulder back into place).  *(#13)*

> The AI's then-current corpus of ethics be explicitly known and inspectable by everyone it is affecting… part of the small, immutable, kernel 'contract' between an AI and its users including not betraying confidences, with exceptions such as if a life were in danger, a subpoena.

**His verdict:** systems *"could be undermined by adversarial attacks that no human would fall prey to"* (Zou et al., 2023).

[2026: Kalai, Nachum, Vempala & Zhang — models guess because training and scoring reward guessing (arXiv:2509.04664).]


---


# 6 · Meet the demands of the task

> Just like a human being working on a task, an AI needs to be responsive enough given the type of problem it is working on. Some applications require microsecond response times… some require real-time human dialogue response times (on the order of ¼ second).  *(#14)* 

> Sufficiently Lingual and Embodied — hear and speak, visually parse scenes and recognize objects, move around, manipulate physical objects, use instruments and devices, sense texture, pressure, temperature, odors.  *(#15)* 

> An AI *"needs to be able to access (and understand) facts they need as they need them.  *(#16)*

**His own concession — this is the criterion on which LLMs win:** *"while Cyc can reason quickly, it is often
not fast enough, certainly not as fast as those LLM-trained chatbots who are able to always respond at
acceptable human conversation speeds"*; and *"While Cyc's KB is both deep and broad, it is often not deep and
broad enough."*

**His conclusion:** *"there are opportunities for the two types to work together… moving us one step further
toward a general AI which is worthy of our trust."*

---

## 


---


## Specification Seems Hard

Mike Dodds at [Software Verification in Lean: Palo Alto 2026](https://luma.com/kytl0zlj?tk=7UBDf5):

https://oath.tech/pub/2026/11/specification-seems-hard/


---


## Lessons from Cyc

# Specification *Is* Hard

> Even with those Cyc-powered KB-building tools, it has taken a coherent team of logicians and programmers four decades, 2000 person-years, to produce the current Cyc KB.  Cycorp's experiments with larger-sized teams generally showed a net decrease in total productivity, due to lack of coherence, deeper reporting chains, and so on.


---

## Semantic Web

Beginning in 1998, Sir Tim Berners-Lee led the effort to create a vision for the future of the web which included publishing the Semantic Web manifesto in Scientific American in 2001.  It built on the ideas of Cyc and addressed its shortcomings which included being closed and inside-out/bottom-up (i.e. a classic application of formal methods) rather than decentralized/local-first, and open like the WWW.

* RDF
* OWL
* N3
* SPARQL
* SHACL


---

## Knowledge Graphs for LLM Reasoning-Acting (ReAct) Agents

GraphRAG uses KG retrieval to improve RAG quality for LLM agent contexts.

LLMs also widely used for constructing and populating KGs.

---


## Constructed Natural Languages for Code Review

*GFLean: An Autoformalisation Framework for Lean via GF*
https://arxiv.org/abs/2404.01234

https://github.com/pkshashank/GFLeanTransfer
https://pkshashank.github.io/

https://github.com/medovina/natural_lean


---


## The Verified Stack

Milawa + Jitawa

https://github.com/jimwhite/milawa-on-jitawa

WASM Spec in ACL2 by Ray Myers
https://github.com/raymyers/wasm-acl2
Talk on Tuesday

WASM Engine correct-by-constuction using Kestrel ACL2-to-C (ATC).
https://github.com/jimwhite/wasm-acl2/tree/main/codegen

A Jitawa (Milawa CL subset) for WASM

ACL2 Spec for RISC-V also promising as RISC-V is popular ISA for trusted compute.


---

## The ACL2 Verified ReAct Agent

```
def do_agent_turn(state, input):
  state = add_input(state, intput)
  while true:
    state = call_llm(state)
    if !has_action(state.response):
      return state
    state = do_actions(state)
```

An agent loop with correct-by-construction "guardrails" by being implemented in ACL2.
https://github.com/wiki3-ai/verified-agent

Checks that actions are allowed but no assurances about the correctness of the outputs, including code.

TODO: Add support dynamic/extensible/contextual rule (i.e. theorem) sets.

---

## 

---


## A Trustworthy Semantic Web Agent

An agent loop which uses transparent and interpretable information in a KG to make verifiably correct decisions and actions.  

Only use language models for natural language to formal language (NL2FL aka autoformalization).  These models can be far smaller than the powerful models used for coding.  They also only need contexts of natural/human size in order to perform local inference necessary for NLU.

Formal methods for validating KG ontology updates from LLM agents.
https://github.com/fabio-rovai/open-ontologies



---

## Software **Is** Speech

This is not the first time fear mongers have instigated government action to violate our rights in America.  

> They can promise strong encryption. They just need to figure out how they can provide us plain text. - FBI General Counsel Valerie Caproni, September 27, 2010

> [W]e're in favor of strong encryption, robust encryption. The country needs it, industry needs it. We just want to make sure we have a trap door and key under some judge's authority where we can get there if somebody is planning a crime. - FBI Director Louis Freeh, May 11, 1995

In the early 90s the US government designated encryption software as a "munition" to be regulated for national security purposes with intensive export restrictions.  EFF represented Daniel Bernstein and got those unconstitutional regulations overturned which paved the way for international e-commerce.

https://www.eff.org/deeplinks/2015/04/remembering-case-established-code-speech


---

## "Slowing Down" Is **Not** An Option

We're at risk to many losses as a consequence of disruptive AI technology (which Andrew Ng called ["The New Electricity" in 2017](https://www.gsb.stanford.edu/insights/andrew-ng-why-ai-new-electricity)), just as we continue to be as a result of other titanic advances in human history such as the discovery of applications for fire, electricity, and nuclear reactions.

Many of these risks are due to the massive technical debt created by humans building computer systems over the last 70 years but any attempts to "slow down" or regulate progress will only apply to the law-abiding defenders which means the only effect will be to make their ability to counter the attackers will be slower and less effective.


<script>
/* Autoscale: shrink any slide whose content overflows the 1280x720 canvas.
   Requires "markdown.marp.html": "all" in VS Code settings (scripts are
   stripped otherwise). Works in preview and in HTML/PDF export. */
(function () {
  var MIN = 0.55;   // never shrink below 55% of the base font size
  var STEP = 0.94;  // shrink ~6% per iteration

  function overflows(section) {
    // scrollHeight includes padding and captures downward overflow.
    // Also catch upward clipping from flex centering (first child above 0).
    if (section.scrollHeight > section.clientHeight + 2) return true;
    var first = section.firstElementChild;
    if (first && first.getBoundingClientRect().top < section.getBoundingClientRect().top - 2) {
      return true;
    }
    return false;
  }

  function fit(section) {
    section.style.fontSize = '';
    var base = parseFloat(getComputedStyle(section).fontSize);
    var size = base;
    for (var i = 0; i < 40 && size > base * MIN; i++) {
      if (!overflows(section)) break;
      size = Math.max(base * MIN, size * STEP);
      section.style.fontSize = size + 'px';
    }
  }

  function run() {
    document.querySelectorAll('section').forEach(fit);
  }

  function start() {
    run();
    // Re-fit once webfonts have settled (metrics change after load).
    if (document.fonts && document.fonts.ready) {
      document.fonts.ready.then(run);
    }
    setTimeout(run, 300);
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', start);
  } else {
    start();
  }
  window.addEventListener('resize', run);
})();
</script>
