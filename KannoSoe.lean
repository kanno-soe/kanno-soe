import KannoSoe.Signature
import KannoSoe.Meta

/-!
Root module for the `KannoSoe` library.

Layers:
* `Signature.V2`: components, Mutual Dependence, reachability,
  joinability, interdependence, and certified chains.
* `Signature.Rules`: finite rule presentations and verified executable
  decision procedures for the core predicates.
* `Signature.Interpenetration`: closed- and open-prime presentations.
* `Meta.Examples`: the finite tea example and executable regression facts.
* `Meta.ReachabilityExamples`: tests for middle-component reach and reversal
  invariance.
* `Meta.InterpenetrationExamples`: base/prime contrast examples.

`Meta.Audit` is a standalone audit target rather than a root import. The
philosophical account lives in `Exposition/Theory.md`, outside the Lean module
graph.
-/
