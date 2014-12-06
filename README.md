# Polyvariant Flow Analysis with Higher-ranked Polymorphic Types and Higher-order Effect Operators

This is an implementation of the analysis named [Polyvariant Flow Analysis with Higher-ranked Polymorphic Types and Higher-order Effect Operators](http://dl.acm.org/citation.cfm?id=1863554) created by Jurriaan Hage and Stefan Holdermans. A demo of this implementation is hosted at: [http://netowork.herokuapp.com/stuff/polyvariant/](http://netowork.herokuapp.com/stuff/polyvariant/).

## Instructions
This program requires [https://github.com/ghcjs/ghcjs](GHCJS) since only a web user interface is supported. The program can still be compiled with GHC and loaded via GHCI. The reconstruction algorithm can be invoked with the examples of the package __Analysis.Examples__. When building using GHCJS, node.js is required and the build process only works in unix based system (sorry, but copyFile from __System.Directory__ is not supported by GHCJS).

The package can be installed by invoking:
```
cabal install
```
in the source directory. This will create a folder inside the binary directory of your cabal directory named "Experimentation-Project.jsexe". Inside this folder there is a file called "index.html". This file can be opened in a modern web browser and will load the complete user interface to use the program.

The user interface contains a text field, buttons for examples, a button to compile the input and a checkbox to decide wether the expression should be reduced to its normal form or not. Note that one should only check this box if the expression has a normal form. Otherwise the browser will get stuck in an infinite loop.

After entering an expression (sample expressions can be written by clicking one of the example buttons), the expression can be compiled. The result will be a list of error messages (if the expression is invalid or does not typecheck) or the type of the expression, the effects that the expression contains, the pretty print of the expression, the reduced expression (if the option was ticked) and two logs of the result. Both logs contain the same information, the double pane is added so it's easier to browse the logs. Be patient because typesetting long expressions (and their logs) can take a lot of time.

The test suite can be run with GHC. It requires __test-framework__ and __test-framework-quickcheck2__ to be installed.