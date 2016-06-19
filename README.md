# First Order Logic Resolution Theorem Prover

A first-order logic theorem prover which uses resolution and displays every step of the resolution process, written in SML.

Load by loading sml and then running:
CM.make "prover.cm"

After that you can resolve formulas by calling
Resolution.resolution Examples.f
where f is the formula you want to resolve. More formulas can be added in the examples.sml file.
