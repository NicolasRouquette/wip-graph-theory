# WIP in graph theory.

This repository is for the purpose of coordinating bleeding-edge work in using Mathlib for proving theorems about graph theory.
As of [Mathlib v4.26.0-rc2](https://github.com/leanprover-community/mathlib4/releases/tag/v4.26.0-rc2), there are insufficient theorems to prove a result I need in my application.

The gist of the problem is described in this Leanprover zulip chat thread: [mathlib4> Proving Graph-Theoretic Properties for Quiver Paths](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Proving.20Graph-Theoretic.20Properties.20for.20Quiver.20Paths)

Matteo Copollina offered a useful suggestion based on his work-in-progress on [Formalization of Markov Chain Monte Carlo in Lean 4](https://github.com/or4nge19/MCMC)

Although Matteo's code does not work yet with v4.26.0-rc2 of Lean and Mathlib, there's enough that I managed to assume his theorems as axioms to prove the Quiver path properties I need.

With the help of Github Copilot and Claude Opus 4.5 preview, we successfully bridged the Prop/Type universe gap between PathWithLength (a Prop-valued path structure used for specifications) and Quiver.Path (a Type-valued structure from Mathlib needed for graph theory). The key challenge was that Lean's universe restrictions prevent direct elimination from Prop to Type. We solved this by: (1) creating PathWithLengthData, a Type-valued analog of PathWithLength with the same structure; (2) using Classical.choice via PathWithLength.toData to extract Type-level witness data from Prop proofs; (3) implementing bidirectional conversions between PathWithLengthData and Quiver.Path using a custom quiverOfRel Quiver instance built from PLift; and (4) adding a new axiom quiver_shortest_path_bound (justified by the MCMC library's isStrictlySimple_of_shortest and length_lt_card_of_isStrictlySimple lemmas) to prove that any path with positive length has a shorter path with length < vertex count. This enabled the completion of pathWithLength_bounded_by_card, which proves that any PathWithLength in a finite type has a bounded-length alternativea key result for DFS termination proofs in Computable.lean.
