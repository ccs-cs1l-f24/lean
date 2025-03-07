
# An Exploration of Interactive Theorem Proving in Lean

The following writeup is a summary of the progress that I made on exploring the Lean interactive proof verification language. 

## The Natural Number Game

I started by completing the Natural Number Game (https://adam.math.hhu.de/#/g/leanprover-community/nng4), an introductory game where the goal is to prove some statements about the natural numbers from the Peano axioms. The game slowly introduces players both to the proofs of various properties of the natural numbers and the general structure of lean proofs. In particular, it explains the framework lean uses of starting with a "goal" statement and transforming it using given results into the statement "True". 

The main tools I learned from playing this game were the `rw` and `apply` tactics (used to rewrite expressions and apply theorems, respectively). Additionally, I learned some philosophical lessons about lean, in particular that sometimes the most "obvious" statements can be the hardest to prove. For instance, I had a lot of trouble converting a statement that "an integer with certain properties exists" to a form where I could use that integer to do other computations.

## Proving that $\sqrt{2}$ is Irrational

## Proving that there are Infinitely Many Primes
