# 2-Coloring Cycles in One Round: Formalization in Lean 4

This repository contains a Lean 4 formalization of the results reported in the manuscript **Brief Announcement: 2-Coloring Cycles in One Round**.

## Result

We show that there is a one-round randomized distributed algorithm that can 2-color cycles such that the expected fraction of monochromatic edges is less than 0.24118. We also show that a one-round algorithm cannot achieve a fraction less than 0.23879. Before this work, the best upper and lower bounds were 0.25 and 0.2.

This repository formalizes the result in the [Lean 4 proof assistant](https://lean-lang.org).

## Remarks

Our proof was largely discovered, developed, and formalized by large language models. We used primarily [Codex](https://openai.com/codex/) with [GPT-5.2](https://openai.com/index/introducing-gpt-5-2/) in [this Docker sandbox](https://github.com/suomela/cursor-sandbox), where the agent was able to interact with Lean, Python, numerous solver libraries, and other computational tools.

## What to read

To understand exactly what is formalized here, it is enough to read these two files (less than 200 lines in total):

- [Distributed2Coloring/Definitions.lean](Distributed2Coloring/Definitions.lean) (what the objects mean)
- [Distributed2Coloring/MainResults.lean](Distributed2Coloring/MainResults.lean) (what is proved about them)

## Building

To verify the proofs with Lean 4, run:

```sh
lake exe cache get
lake build
```

Note that this is a large project, with 17000+ lines of code, and it aims at being 100% kernel-checked. Hence compiling it from scratch may take a while (tens of minutes).

## Contact information

- Primary contact: [Jukka Suomela](https://jukkasuomela.fi)
